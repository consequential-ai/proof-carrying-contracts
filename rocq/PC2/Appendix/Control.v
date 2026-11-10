(** * Appendix C: a design for the control step

The routine of §3.5.1 for any contract: it decides on the state it starts from,
with decidable tests [Ready], [Act] and [Fix]; it starts the contract or leaves
it inactive, idles, fixes, or terminates. The conditions of App. C
("Establishing the certificate") give A3. Then the compute budget of App. C,
whose certificate is arithmetic. *)

From Stdlib Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq zify.
From PC2 Require Import Basic Airlock Execution Compliance Completion.

Unset Printing Implicit Defensive.

Import Contract.

Module Design.

(** **A control design** (§3.5.1): its tests, and the models of its branches
([doFix] for the paper's [fix], a keyword of Rocq). *)
Record t (S : Type) (K : Contract S) := Build {
  Ready : S -> bool;
  Act : S -> bool;
  Fix : S -> bool;
  init : S -> S -> Prop;
  noStart : S -> S -> Prop;
  idle : S -> S -> Prop;
  doFix : S -> S -> Prop;
  term : S -> S -> Prop;
}.

Arguments t {S} K.
Arguments Build {S K} Ready Act Fix init noStart idle doFix term.
Arguments Ready {S K} _ _.
Arguments Act {S K} _ _.
Arguments Fix {S K} _ _.
Arguments init {S K} _ _ _.
Arguments noStart {S K} _ _ _.
Arguments idle {S K} _ _ _.
Arguments doFix {S K} _ _ _.
Arguments term {S K} _ _ _.

Section Design.

Variables (S : Type) (K : Contract S) (D : t K).

(** The model of the routine of §3.5.1, deciding on the state it starts from. *)
Definition model (s s' : S) : Prop :=
  if stop K s then (if Ready D s then init D s s' else noStart D s s')
  else if Act D s then (if Fix D s then doFix D s s' else term D s s')
  else idle D s s'.

(** **The conditions of App. C.** Outside [Act], a compliant active state is in
[C_idle] (one idle period keeps [C]); in [Act ∩ Fix] the fix keeps [C]; in [End
= Act ∖ Fix] termination keeps [C] until the contract closes; each branch is
enabled where it is selected; from [Ready], initialization lands in [C];
elsewhere the contract stays inactive. *)
Record Sound : Prop := {
  idle_ok : forall s, Active K s -> C K s -> ~~ Act D s -> wp (idle D) (C K) s;
  fix_ok : forall s, Active K s -> C K s -> Act D s -> Fix D s ->
    wp (doFix D) (C K) s;
  term_ok : forall s, Active K s -> C K s -> Act D s -> ~~ Fix D s ->
    wp (term D) (C K) s;
  init_ok : forall s, stop K s -> Ready D s ->
    (exists s', init D s s') /\ forall s', init D s s' -> Active K s' -> C K s';
  noStart_ok : forall s, stop K s -> ~~ Ready D s ->
    (exists s', noStart D s s') /\ forall s', noStart D s s' -> stop K s';
}.

(** **The certificate from the design** (App. C): a contract whose control step
follows a sound design satisfies A3. *)
Theorem cert : (forall s s', ctrl K s s' <-> model s s') -> Sound -> Cert K.
Proof.
move=> hctrl h; split.
- move=> s ha hc; have hm := fun s' => hctrl s s'.
  rewrite /model (negbTE ha) /= in hm; apply: (wp_of_iff hm).
  case hact: (Act D s); last exact: (idle_ok h _ ha hc (negbT hact)).
  case hfix: (Fix D s); first exact: (fix_ok h _ ha hc hact hfix).
  exact: (term_ok h _ ha hc hact (negbT hfix)).
- move=> s s' hin ha' /(hctrl s s'); rewrite /model hin.
  case hr: (Ready D s) => hs; first exact: (init_ok h _ hin hr).2 s' hs ha'.
  by case/negP: ha'; exact: (noStart_ok h _ hin (negbT hr)).2 s' hs.
- move=> s hin; case hr: (Ready D s);
    [have [s' hs'] := (init_ok h _ hin hr).1
    | have [s' hs'] := (noStart_ok h _ hin (negbT hr)).1];
    by exists s'; apply/hctrl; rewrite /model hin hr.
Qed.

End Design.

Arguments model {S K} D s s'.
Arguments Sound {S K} D.
Arguments cert {S K} D _ _.

End Design.

(** ** The compute budget (App. C) *)

Module ComputeBudget.

(** The state: the bill [b], a bound [r] on the charging rate of the running
jobs, the remaining shutdown allowance [h], the time [time], and the label. *)
Record St := MkSt {
  b : nat;
  r : nat;
  h : nat;
  time : nat;
  ℓ : Label;
}.

Section Budget.

Variables (B d p : nat).

(** The clause: the bill, with the maximum charge while the jobs stop, stays
within the budget, at every instant, closing included; while the contract is
ongoing, the time is within the deadline. The reserve [r * h] is for the budget:
the jobs are charged until they have stopped. *)
Definition C (s : St) : Prop :=
  b s + r s * h s <= B /\ (ℓ s = Ongoing -> time s <= d).

(** The waiting tests, which certify [C_idle]: one more period, and a shutdown
after it, stay within the budget and before the deadline. *)
Definition waitOK (s : St) : bool :=
  (b s + r s * (p + h s) <= B) && (time s + p + h s <= d).

(** Outside changes during [u ≤ p] units of waiting: the bill rises at most at
rate [r], jobs may stop, time advances; the label is kept. *)
Definition idle (s s' : St) : Prop :=
  exists u, u <= p /\
    [/\ b s' <= b s + r s * u, r s' <= r s, h s' <= h s, time s' = time s + u
      & ℓ s' = ℓ s].

(** Stopping the jobs, after [u ≤ h] units: the bill rises at most at rate [r],
the allowance counts down. *)
Definition shut (s s' : St) : Prop :=
  exists u, u <= h s /\
    [/\ b s' <= b s + r s * u, r s' <= r s, h s' <= h s - u
      & time s' = time s + u].

(** The compute-budget contract: no tool for the agent, the clause [C]; the
control step is the design's. *)
Definition contract : Contract St :=
  @Contract.Build St C St id void (@of_void _) (fun _ _ => False)
    (fun s => ℓ s != Ongoing).

(** The control design, closing first: start only where the waiting tests hold;
idle where they hold; where only the budget test fails, fix by stopping the jobs
and staying ongoing; where the time test fails, close the contract at once, and
stop the jobs with the contract closed. *)
Definition design : Design.t contract :=
  Design.Build (fun s => waitOK s && (ℓ s == Pending)) (fun s => ~~ waitOK s)
    (fun s => time s + p + h s <= d)
    (fun s s' => s' = s \/ s' = MkSt (b s) (r s) (h s) (time s) Ongoing)
    (fun s s' => s' = s) idle (fun s s' => shut s s' /\ ℓ s' = Ongoing)
    (fun s s' => s' = s \/ (ℓ s' = Terminated /\ shut s s')).

(** Stopping the jobs keeps the bill, with the remaining reserve, within its
starting bound, and takes at most the allowance. *)
Lemma shut_C {s s' : St} :
  shut s s' -> b s' + r s' * h s' <= b s + r s * h s /\ time s' <= time s + h s.
Proof.
case=> u [hu [hb hr hh ht]]; split; last by rewrite ht leq_add2l.
apply: leq_trans (leq_add hb (leq_mul hr hh)) _.
by rewrite -addnA -mulnDr subnKC.
Qed.

(** **The compute budget's design is sound**, so the contract satisfies A3: the
certificate is arithmetic, with no reserve of time. *)
Theorem sound : Design.Sound design.
Proof.
split.
- move=> s _ hc /negPn /andP[hb hd].
  split; first by exists s, 0; rewrite muln0; do !split=> //; lia.
  move=> s' [u [hu [hb' hr' hh' ht' hl]]].
  have h1 : r s' * h s' <= r s * h s := leq_mul hr' hh'.
  have h2 : r s * u <= r s * p := leq_mul (leqnn _) hu.
  have h3 : r s * (p + h s) = r s * p + r s * h s := mulnDr _ _ _.
  by split=> [|_]; lia.
- move=> s ha hc _ /= hd.
  have hon : ℓ s = Ongoing by move: ha; rewrite /Active /= negbK => /eqP.
  split; first by exists s; split=> //; exists 0; rewrite muln0;
    do !split=> //; lia.
  move=> s' [hs _]; have [hb' ht'] := shut_C hs.
  by case: hc => hc _; split=> [|_]; lia.
- move=> s _ hc _ _; split; first by exists s; left.
  move=> s' [->|[hl hs]] //; have [hb' _] := shut_C hs.
  by case: hc => hc _; split=> [|]; [lia | rewrite hl].
- move=> s _ /andP[/andP[hb hd] /eqP hp].
  split; first by exists s; left.
  move=> s' [->|->] ha'; first by move: ha'; rewrite /Active /= hp.
  have h3 : r s * (p + h s) = r s * p + r s * h s := mulnDr _ _ _.
  by split=> [/=|/= _]; lia.
- move=> s hin _; split; first by exists s.
  by move=> s' ->.
Qed.

End Budget.

End ComputeBudget.
