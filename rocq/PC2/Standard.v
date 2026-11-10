(** * The standard contract (Example 1)

The template of Example 1, with a deadline. A state is [(x, t, ℓ)]: the task
part, the time as the clock gives it, and the label. The clause is [(B(x) ∧ t ≤
d) ∨ ℓ ≠ ongoing], the view [(View(x), t, ℓ)].

The agent's tools are the task tools, whose models keep the label and let time
advance within a timeout, and settlement, [free_settle|Goal]. The control step
follows §3.5.1, closing first: from [pending] it starts the contract if [Ready]
holds and otherwise leaves it void; from [ongoing] it idles for one period,
unless idling could pass the deadline or a termination condition of the task
holds, and then it terminates. Settlement and termination both close the
contract when they start; the payment or the refund then runs with the contract
closed. No reserve of time is needed (§3.5.1).

Proved here, once for every contract built on the template: A3 ([cert]),
standard form ([standardForm]), what settlement asks ([settle_obligation]), and
the reductions of the agent's obligations used by the examples. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution Compliance Completion.

Unset Printing Implicit Defensive.

Module Standard.

(** The state of a standard contract: the task part, the time as the clock gives
it, the label. *)
Record St (X : Type) := MkSt {
  task : X;
  time : nat;
  label : Label;
}.

Arguments MkSt {X} task time label.
Arguments task {X} _.
Arguments time {X} _.
Arguments label {X} _.

(** A task tool: its input, what it may do to the task part (outside changes
included), and its timeout. *)
Record Task (X : Type) := MkTask {
  Inp : Type;
  Dx : Inp -> X -> X -> Prop;
  dur : Inp -> nat;
}.

Arguments MkTask {X} Inp Dx dur.
Arguments Inp {X} _.
Arguments Dx {X} _ i _ _.
Arguments dur {X} _ i.

(** What a standard contract is made of: the view of the task part; the business
constraints, the goal, the deadline; the task tools; what releasing the escrow
does to the task part; initialization: where control may start the contract (a
decidable test), what starting does, and how long it takes, and what not
starting does; outside changes to the task part while control waits, and the
idle period; the task's own termination conditions (a decidable test), and what
refunding does. *)
Record Spec (X : Type) := MkSpec {
  VX : Type;
  viewX : X -> VX;
  B : X -> Prop;
  Goal : X -> Prop;
  d : nat;
  N : Type;
  tasks : N -> Task X;
  pay : X -> X -> Prop;
  Ready : X -> nat -> bool;
  initX : X -> X -> Prop;
  initDur : nat;
  voidX : X -> X -> Prop;
  out : X -> X -> Prop;
  period : nat;
  endX : X -> bool;
  refund : X -> X -> Prop;
}.

Arguments MkSpec {X} VX viewX B Goal d N tasks pay Ready initX initDur voidX out
  period endX refund.
Arguments VX {X} _.
Arguments viewX {X} _ _.
Arguments B {X} _ _.
Arguments Goal {X} _ _.
Arguments d {X} _.
Arguments N {X} _.
Arguments tasks {X} _ _.
Arguments pay {X} _ _ _.
Arguments Ready {X} _ _ _.
Arguments initX {X} _ _ _.
Arguments initDur {X} _.
Arguments voidX {X} _ _ _.
Arguments out {X} _ _ _.
Arguments period {X} _.
Arguments endX {X} _ _.
Arguments refund {X} _ _ _.

(** The names of a standard contract's tools. *)
Inductive Name (N : Type) := NTask (l : N) | NSettle.

Arguments NTask {N} l.
Arguments NSettle {N}.

Module Spec.

Section Spec.

Variables (X : Type) (sp : Spec X).

(** The tool of a task: the label is kept, and time advances within the timeout.
*)
Definition taskTool (T : Task X) : Tool (St X) :=
  @Tool.Build (St X) (Inp T) (fun i s s' =>
    [/\ label s' = label s, time s <= time s' <= time s + dur T i
      & Dx T i (task s) (task s')]).

(** What [free_settle] may do: nothing yet, or the contract closes as settled
and the escrow is released. *)
Definition settleD (s s' : St X) : Prop :=
  s' = s \/ (label s' = Settled /\ pay sp (task s) (task s')).

(** [free_settle]: the contract closes as settled when settlement starts, then
the escrow is released. *)
Definition freeSettle : Tool (St X) :=
  @Tool.Build (St X) unit (fun _ => settleD).

(** Settlement, [free_settle|Goal] (§3.5.2). *)
Definition settleTool : Tool (St X) :=
  Tool.restrict freeSettle (fun _ s => Goal sp (task s)).

(** Where control must act: idling one more period could pass the deadline, or a
termination condition of the task holds ([Act], §3.5.1). With no fix, [End =
Act]. *)
Definition Act (s : St X) : bool :=
  (d sp < time s + period sp) || endX sp (task s).

(** **The control step** (§3.5.1), deciding on the state it starts from, closing
first. *)
Definition ctrl (s s' : St X) : Prop :=
  match label s with
  | Pending =>
    if Ready sp (task s) (time s) then
      (label s' = Pending /\ task s' = task s) \/
      (label s' = Ongoing /\ initX sp (task s) (task s') /\
         time s' <= time s + initDur sp)
    else s' = s \/ (label s' = Void /\ voidX sp (task s) (task s'))
  | Ongoing =>
    if Act s then
      s' = s \/ (label s' = Terminated /\ refund sp (task s) (task s'))
    else
      [/\ label s' = Ongoing, time s <= time s' <= time s + period sp &
          out sp (task s) (task s')]
  | _ => s' = s
  end.

(** The tools of the contract, by name. *)
Definition tools (l : Name (N sp)) : Tool (St X) :=
  match l with NTask l => taskTool (tasks sp l) | NSettle => settleTool end.

(** **Example 1, the standard contract**, with a deadline. *)
Definition contract : Contract (St X) :=
  @Contract.Build (St X)
    (fun s => (B sp (task s) /\ time s <= d sp) \/ label s <> Ongoing)
    (VX sp * nat * Label)
    (fun s => (viewX sp (task s), time s, label s))
    (Name (N sp)) tools ctrl
    (fun s => label s != Ongoing).

Lemma active_iff (s : St X) : Contract.Active contract s <-> label s = Ongoing.
Proof. by rewrite /Contract.Active /=; case: (label s). Qed.

Lemma C_iff {s : St X} : label s = Ongoing ->
  (Contract.C contract s <-> B sp (task s) /\ time s <= d sp).
Proof. by move=> h /=; rewrite h; split=> [[//|//]|]; left. Qed.

(** The design obligations of the template: starting from [Ready] lands in the
clause, and outside changes while waiting keep the business constraints (and may
change nothing). *)
Record Design : Prop := {
  init_ok : forall x t x' t', Ready sp x t -> initX sp x x' ->
    t' <= t + initDur sp -> B sp x' /\ t' <= d sp;
  out_refl : forall x, out sp x x;
  out_B : forall x x', B sp x -> out sp x x' -> B sp x';
}.

(** **A3 for the standard contract**, once for every contract built on the
template. No reserve of time: where idling could pass the deadline, control
closes the contract at once. *)
Theorem cert (hD : Design) : Contract.Cert contract.
Proof.
split.
- move=> s ha hc; have hℓ := (active_iff s).1 ha.
  have [hB ht] := (C_iff hℓ).1 hc.
  rewrite /wp /= /ctrl hℓ; case hact: (Act s).
    split; first by exists s; left.
    by move=> s' [->|[hl _]] //; right; rewrite hl.
  move/negbT: hact; rewrite negb_or -leqNgt => /andP[htp _].
  split; first by exists s; split=> //;
    [rewrite leqnn leq_addr | exact: out_refl hD _].
  move=> s' [_ /andP[_ ht'] ho]; left; split; first exact: out_B hD _ _ hB ho.
  exact: leq_trans ht' htp.
- move=> s s' /= hin ha'; have hℓ' := (active_iff s').1 ha'.
  rewrite /ctrl; case hs₀: (label s) hin => //= _;
    try by move=> hss; move: hℓ'; rewrite hss hs₀.
  case hr: (Ready sp (task s) (time s)) => /= hs.
    case: hs => [[hl _]|[_ [hi ht]]]; first by rewrite hl in hℓ'.
    by left; exact: init_ok hD _ _ _ _ hr hi ht.
  by case: hs => [hss|[hl _]]; [move: hℓ'; rewrite hss hs₀ | rewrite hl in hℓ'].
- move=> s /= hin; rewrite /ctrl; case hs₀: (label s) hin => //= _;
    try by exists s.
  by case: (Ready sp (task s) (time s)); exists s; left.
Qed.

(** The model of a call of the standard contract, by its name. *)
Lemma D_task (l : N sp) (i : Inp (tasks sp l)) (s s' : St X) :
  Contract.D contract (existT _ (NTask l) i) s s' <->
    [/\ label s' = label s, time s <= time s' <= time s + dur (tasks sp l) i &
      Dx (tasks sp l) i (task s) (task s')].
Proof. by []. Qed.

Lemma D_settle (i : unit) (s s' : St X) :
  Contract.D contract (existT _ NSettle i) s s' <->
    Goal sp (task s) /\ settleD s s'.
Proof. by []. Qed.

(** The model of [free_settle], for every call. *)
Definition freeD (c : Contract.Call contract) : St X -> St X -> Prop := settleD.

Lemma sf_settle_model (c : Contract.Call contract) : projT1 c = NSettle ->
  forall s s', Contract.D contract c s s' <-> Goal sp (task s) /\ freeD c s s'.
Proof. by case: c => l i /= hl; subst l. Qed.

Lemma sf_settle_label (c : Contract.Call contract) : projT1 c = NSettle ->
  forall s s', freeD c s s' -> label s' = label s \/ label s' = Settled.
Proof. by move=> _ s s' [->|[hl _]]; [left | right]. Qed.

Lemma sf_tools_label (c : Contract.Call contract) (s s' : St X) :
  Contract.D contract c s s' -> label s' = label s \/ projT1 c = NSettle.
Proof. by case: c => [[l|] i] /= => [[hl _]|_]; [left | right]. Qed.

Lemma sf_ctrl_pending (s s' : St X) :
  label s = Pending -> Contract.ctrl contract s s' ->
  [\/ label s' = Ongoing /\ Ready sp (task s) (time s), label s' = Pending |
      label s' = Void /\ ~ Ready sp (task s) (time s)].
Proof.
move=> hp; rewrite /= /ctrl hp.
case hr: (Ready sp (task s) (time s)) => /= hs.
  by case: hs => [[hl _]|[hl _]]; [constructor 2 | constructor 1].
by case: hs => [->|[hl _]]; [constructor 2 | constructor 3].
Qed.

Lemma sf_ctrl_ongoing (s s' : St X) :
  label s = Ongoing -> Contract.ctrl contract s s' ->
  label s' = Ongoing \/ (label s' = Terminated /\ Act s).
Proof.
move=> ho; rewrite /= /ctrl ho.
case hact: (Act s) => /= hs; last by left; case: hs.
by case: hs => [->|[hl _]]; [left | right].
Qed.

(** **The standard contract is in standard form.** *)
Definition standardForm : StandardForm contract := {|
  StandardForm.lab := label;
  StandardForm.active_iff := active_iff;
  StandardForm.settle := NSettle;
  StandardForm.Goal s := Goal sp (task s);
  StandardForm.freeD := freeD;
  StandardForm.settle_model := sf_settle_model;
  StandardForm.settle_label := sf_settle_label;
  StandardForm.tools_label := sf_tools_label;
  StandardForm.Ready s := Ready sp (task s) (time s);
  StandardForm.Ends s := Act s;
  StandardForm.ctrl_pending := sf_ctrl_pending;
  StandardForm.ctrl_ongoing := sf_ctrl_ongoing;
|}.

(** **Proposition 1 for the standard contract**: settling asks exactly the goal
over the window. Since settlement closes the contract when it starts,
[free_settle] is admissible at every compliant active state, deadline included.
*)
Theorem settle_obligation (hD : Design) (n : nat) (v : Contract.V contract) :
  Contract.OblN contract n (existT _ NSettle tt) v <->
    forall s s', Contract.Active contract s -> Contract.Active contract s' ->
      Contract.view contract s = v -> Contract.C contract s ->
      Contract.Win contract n s s' -> Goal sp (task s').
Proof.
apply: (Completion.settle_obligation (cert hD) (fun s => Goal sp (task s))
  settleD (existT _ NSettle tt) (D_settle tt)).
move=> s _ hc _; split; first by exists s; left.
by move=> s' [->|[hl _]] //; right; rewrite hl.
Qed.

(** Outside changes over any number of idle periods. *)
Inductive OutStar : X -> X -> Prop :=
  | outStar_refl (x : X) : OutStar x x
  | outStar_step (x y z : X) : OutStar x y -> out sp y z -> OutStar x z.

(** The window of an ongoing state of the standard contract: at most [n] idle
periods, through ongoing states. *)
Lemma win_bound {n : nat} {s s' : St X} :
  Contract.Win contract n s s' -> label s' = Ongoing ->
  [/\ label s = Ongoing, time s <= time s' <= time s + n * period sp
    & OutStar (task s) (task s')].
Proof.
elim: n s' => [|n ih] s' /=.
  by move=> <- ha'; split=> //;
    [rewrite mul0n addn0 leqnn | exact: outStar_refl].
have hmul (a : nat) :
    a <= time s + n * period sp -> a <= time s + n.+1 * period sp.
  by move=> h; apply: (leq_trans h); rewrite leq_add2l leq_mul2r leqnSn orbT.
case=> [hw|[u [hu hw hc]]] ha'.
  by have [h1 /andP[h2 h3] h4] := ih _ hw ha'; split=> //; rewrite h2 hmul.
have huℓ := (active_iff u).1 hu.
have [h1 /andP[h2 h3] h4] := ih _ hw huℓ.
move: hc; rewrite /= /ctrl huℓ; case hact: (Act u) => /= hc.
  case: hc => [hus|[hl _]]; last by rewrite hl in ha'.
  by rewrite hus; split=> //; rewrite h2 hmul.
case: hc => _ /andP[ht ht'] ho; split=> //; last exact: outStar_step h4 ho.
rewrite (leq_trans h2 ht) /=; apply: leq_trans ht' _.
by rewrite mulSnr addnA leq_add2r.
Qed.

(** **What a task call asks, sufficiently**: at a view [(vx, t, ongoing)], a
call within its timeout before the deadline, after [n] idle periods, that keeps
the business constraints from every hidden task part the agent cannot rule out,
after any outside changes, and is enabled. *)
Theorem oblN_task (hD : Design) {n : nat} {l : N sp} {i : Inp (tasks sp l)}
    {vx : VX sp} {t : nat} :
  t + n * period sp + dur (tasks sp l) i <= d sp ->
  (forall x x₁ x₂, viewX sp x = vx -> B sp x -> OutStar x x₁ -> B sp x₁ ->
    Dx (tasks sp l) i x₁ x₂ -> B sp x₂) ->
  (forall x₁, exists x₂, Dx (tasks sp l) i x₁ x₂) ->
  Contract.OblN contract n (existT _ (NTask l) i) (vx, t, Ongoing).
Proof.
move=> htime hB hen s s' ha ha' hv hc hw.
have hℓ' := (active_iff s').1 ha'.
have [hℓ /andP[hts ht'] hout] := win_bound hw hℓ'.
move: hv => /= [hvx hts₀ _].
have hBs := ((C_iff hℓ).1 hc).1.
have hBs' := ((C_iff hℓ').1 (Contract.win_C (cert hD) hc hw)).1.
have [x₂ hx₂] := hen (task s').
split.
  by exists (MkSt x₂ (time s') (label s')); split=> //=; rewrite leqnn leq_addr.
move=> s'' [hl /andP[_ ht''] hd]; left; split;
  first exact: hB _ _ _ hvx hBs hout hBs' hd.
apply: leq_trans ht'' (leq_trans _ htime); rewrite leq_add2r -hts₀; exact: ht'.
Qed.

(** **A task call that can break the business constraints is rejected**: if,
from some compliant task part with the view [vx], the call may lead to a task
part that breaks them, its obligation is false, whatever the allowance, so no
proof is accepted. *)
Theorem not_oblN_task {n : nat} {l : N sp} {i : Inp (tasks sp l)}
    {vx : VX sp} {t : nat} :
  t <= d sp -> forall x x₂ : X, viewX sp x = vx -> B sp x ->
  Dx (tasks sp l) i x x₂ -> ~ B sp x₂ ->
  ~ Contract.OblN contract n (existT _ (NTask l) i) (vx, t, Ongoing).
Proof.
move=> ht x x₂ hv hB hd hB₂ h.
have ha : Contract.Active contract (MkSt x t Ongoing) by apply/active_iff.
have hv' : Contract.view contract (MkSt x t Ongoing) = (vx, t, Ongoing)
  by rewrite /= hv.
have hadm := h _ _ ha ha hv' (or_introl (conj hB ht)) Contract.win_refl.
have hD' : Contract.D contract (existT _ (NTask l) i) (MkSt x t Ongoing)
    (MkSt x₂ t Ongoing).
  by split=> //=; rewrite leqnn leq_addr.
by case: (hadm.2 _ hD') => [[/hB₂]|[]].
Qed.

(** **Settling before the goal holds is rejected**: if some compliant task part
with the view [vx] does not satisfy the goal, the settlement obligation is
false, whatever the allowance. *)
Theorem not_oblN_settle {n : nat} {vx : VX sp} {t : nat} :
  t <= d sp -> forall x : X, viewX sp x = vx -> B sp x -> ~ Goal sp x ->
  ~ Contract.OblN contract n (existT _ NSettle tt) (vx, t, Ongoing).
Proof.
move=> ht x hv hB hG h.
have ha : Contract.Active contract (MkSt x t Ongoing) by apply/active_iff.
have hv' : Contract.view contract (MkSt x t Ongoing) = (vx, t, Ongoing)
  by rewrite /= hv.
have [[s'' [hg _]] _] :=
  h _ _ ha ha hv' (or_introl (conj hB ht)) Contract.win_refl.
exact: hG hg.
Qed.

(** **Settling once the goal holds**: at a view [(vx, t, ongoing)], if every
compliant task part with that view satisfies the goal, and outside changes keep
it, the settlement obligation holds for every allowance. *)
Theorem oblN_settle (hD : Design) {n : nat} {vx : VX sp} {t : nat} :
  (forall x x₁, viewX sp x = vx -> B sp x -> OutStar x x₁ -> Goal sp x₁) ->
  Contract.OblN contract n (existT _ NSettle tt) (vx, t, Ongoing).
Proof.
move=> hG; apply/(settle_obligation hD n (vx, t, Ongoing)).
move=> s s' _ ha' hv hc hw.
have hℓ' := (active_iff s').1 ha'.
have [hℓ _ hout] := win_bound hw hℓ'.
move: hv => /= [hvx _ _].
exact: hG _ _ hvx ((C_iff hℓ).1 hc).1 hout.
Qed.

(** The standard contract keeps its clock within the deadline while it is
active. *)
Lemma deadline_clause (s : St X) :
  Contract.Active contract s -> Contract.C contract s -> time s <= d sp.
Proof. by move=> ha hc; exact: ((C_iff ((active_iff s).1 ha)).1 hc).2. Qed.

End Spec.

Arguments taskTool {X} T.
Arguments settleD {X} sp s s'.
Arguments freeSettle {X} sp.
Arguments settleTool {X} sp.
Arguments Act {X} sp s.
Arguments ctrl {X} sp s s'.
Arguments tools {X} sp l.
Arguments contract {X} sp.
Arguments active_iff {X} sp s.
Arguments C_iff {X} sp {s} _.
Arguments Design {X} sp.
Arguments cert {X} sp hD.
Arguments D_task {X} sp l i s s'.
Arguments D_settle {X} sp i s s'.
Arguments freeD {X} sp c s s'.
Arguments standardForm {X} sp.
Arguments settle_obligation {X} sp hD n v.
Arguments OutStar {X} sp _ _.
Arguments outStar_refl {X sp} x.
Arguments outStar_step {X sp x y z} _ _.
Arguments win_bound {X} sp {n s s'} _ _.
Arguments oblN_task {X} sp hD {n l i vx t} _ _ _.
Arguments not_oblN_task {X} sp {n l i vx t} _ x x₂ _ _ _ _.
Arguments not_oblN_settle {X} sp {n vx t} _ x _ _ _.
Arguments oblN_settle {X} sp hD {n vx t} _.
Arguments deadline_clause {X} sp s _ _.

End Spec.

End Standard.
