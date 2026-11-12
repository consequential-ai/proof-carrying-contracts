(** * Completion (§4.2): Theorem 2 and Proposition 1, and the agent tools of
§3.5.2

A contract is in **standard form** (Example 1) when its label says whether it is
active, its settlement tool is [free_settle|Goal], only control and settlement
change the label, control starts the contract only from a [Ready] state and
terminates it only from a state in [End], and settlement only settles. Theorem 2
holds for every contract in standard form; the template of Example 1
([Standard]) is one. *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution Compliance.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

(** The status of a standard contract (Example 1). *)
Inductive Label := Pending | Ongoing | Settled | Terminated | Void.

Definition label_eqb (a b : Label) : bool :=
  match a, b with
  | Pending, Pending | Ongoing, Ongoing | Settled, Settled
  | Terminated, Terminated | Void, Void => true
  | _, _ => false
  end.

Lemma label_eqP : Equality.axiom label_eqb.
Proof. by case; case; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build Label label_eqP.

Module StandardForm.

(** **Standard form (Example 1).** The facts about a contract that Theorem 2
uses, on the models: the label [lab] (held by the Airlock) is [Ongoing] exactly
on the active states; the goal, [Ready] and [End] are tests; the settlement
tool's model is the goal as a precondition
on [free_settle], which can only settle; the other tools leave the label
unchanged; from [Pending], control makes the contract ongoing only from a
[Ready] state and otherwise leaves it pending or void; from [Ongoing], control
keeps it ongoing, or terminates it, only from a state in [End] (here [Ends],
[End] being a keyword of Rocq).

That the other tools leave the label unchanged is stated as: a call either keeps
the label or is settlement ([tools_label]); this is the Lean statement [c.1 ≠
settle → lab s' = lab s] without the case analysis on whether a tool is
settlement, which needs no decidable names here. *)
Record t (S : Type) (K : Contract S) := Build {
  lab : S -> Label;
  activeE : forall s, Active K s = (lab s == Ongoing);
  settle : Name K;
  Goal : pred S;
  freeD : Call K -> S -> S -> Prop;
  settle_model : forall c : Call K, projT1 c = settle ->
    forall s s', D K c s s' <-> Goal s /\ freeD c s s';
  settle_label : forall c : Call K, projT1 c = settle ->
    forall s s', freeD c s s' -> lab s' = lab s \/ lab s' = Settled;
  tools_label : forall (c : Call K) s s', D K c s s' ->
    lab s' = lab s \/ projT1 c = settle;
  Ready : pred S;
  Ends : pred S;
  ctrl_pending : forall s s', lab s = Pending -> ctrl K s s' ->
    [\/ lab s' = Ongoing /\ Ready s, lab s' = Pending |
        lab s' = Void /\ ~~ Ready s];
  ctrl_ongoing : forall s s', lab s = Ongoing -> ctrl K s s' ->
    lab s' = Ongoing \/ (lab s' = Terminated /\ Ends s);
}.

End StandardForm.

Abbreviation StandardForm := StandardForm.t.

Import StandardForm.

Section Completion.

Variables (S : Type) (K : Contract S) (P W : Type) (ch : Checker P) (πK : P)
  (E : Effects K W).

Lemma next_record {x : Vars K P} {inp : Input K P} {o : Op K P}
  {κ : S -> Vars K P} :
  Next K ch πK x inp o κ -> forall s, record (κ s) = s.
Proof. by case. Qed.

(** The only variables of an execution in the initial phase are the starting
ones. *)
Lemma exec_init {s₀ : S} {w : W} {x : Vars K P}
  {xs : seq (Op K P * Segment W S)} :
  Exec K ch πK E s₀ w x xs -> phase x = Init -> record x = s₀ /\ xs = [::].
Proof.
case=> [//|{}w {}x {}xs inp o κ σ l _ hn _ _ hx].
by exfalso; exact: next_phase hn _ hx.
Qed.

(** An operation that Algorithm 1 invokes after initialization starts from an
active state. *)
Lemma next_active {x : Vars K P} {inp : Input K P} {o : Op K P}
  {κ : S -> Vars K P} :
  Next K ch πK x inp o κ -> phase x <> Init -> Active K (record x).
Proof. by case=> // {}x {}inp hx _ _ hne; exfalso; exact: hne hx. Qed.

(** Initialization is a control step. *)
Lemma next_init_ctrl {x : Vars K P} {inp : Input K P} {o : Op K P}
  {κ : S -> Vars K P} :
  Next K ch πK x inp o κ -> phase x = Init -> o = OpCtrl.
Proof. by case=> // {}x x₂ {}inp q hx _ _ _ _ _ hx'; rewrite hx in hx'. Qed.

(** Initialization starts from an inactive state. *)
Lemma next_init_inactive {x : Vars K P} {inp : Input K P} {o : Op K P}
  {κ : S -> Vars K P} :
  Next K ch πK x inp o κ -> phase x = Init -> stop K (record x).
Proof.
by case=> {}x => [? _ _ //|? ? ? hx _ _ _ _ _|? ? hx _ _ _|? hx _] /=;
  rewrite hx.
Qed.

(** **Theorem 2 (Completion).** Under A1 and A2, for a contract in standard form
created pending, in every execution of Algorithms 1–2 the label of the last
reading says how the contract ended, in exactly one way:
1. _void_ (or still pending): the conditions to start did not hold, and no tool
   call was made;
2. _settled_: the last operation was the settlement, which started from a state
   where the goal held;
3. _terminated_: the last operation was a control step, which started from a
   state in [End], where the control step found a termination condition. *)
Theorem completion (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (F : StandardForm K) {s₀ : S} :
  lab F s₀ = Pending ->
  forall {w : W} {x : Vars K P} {xs : seq (Op K P * Segment W S)},
  Exec K ch πK E s₀ w x xs ->
  [/\ lab F (record x) = Pending \/ lab F (record x) = Void ->
        forall j p, onth xs j = Some p -> p.1 = OpCtrl,
      lab F (record x) = Settled ->
        exists xs' q σ, [/\ xs = rcons xs' (OpCall q, σ),
          projT1 (call q) = settle F & Goal F (pt σ (first σ)).2]
    & lab F (record x) = Terminated ->
        exists xs' σ, xs = rcons xs' (OpCtrl, σ) /\ Ends F (pt σ (first σ)).2].
Proof.
move=> hs₀ w x xs; case=> [w₀|w' x' xs' inp o κ σ l hprev hn hfirst he].
  by rewrite /= hs₀; split=> // _ j p; rewrite onth0n.
have [hI hph _] := exec_inv hA1 hA2 hprev.
have [hen _] := next_safe hA1 hI hn.
have hD : model o (record x') (pt σ l).2 := coverage_op hA2 hen (he l).
have hstart : (pt σ (first σ)).2 = record x' by rewrite hfirst.
rewrite (next_record hn); case: (eqVneq (phase x') Init) => [hinit|/eqP hne].
  (* the last operation is the initialization, from [s₀] *)
  have [hr₀ ->] := exec_init hprev hinit.
  have ho := next_init_ctrl hn hinit; subst o.
  have hpend : lab F (record x') = Pending by rewrite hr₀.
  split; first by move=> _ j p /onth1P[_ <-].
    by case: (ctrl_pending F _ _ hpend hD) => [[-> _]|->|[-> _]].
  by case: (ctrl_pending F _ _ hpend hD) => [[-> _]|->|[-> _]].
have hon : lab F (record x') = Ongoing.
  by apply/eqP; rewrite -activeE; exact: next_active hn hne.
case: o hn hD he hen => [|q] hn hD he _.
  (* a control step from an ongoing state *)
  case: (ctrl_ongoing F _ _ hon hD) => [->|[-> hE]]; first by split=> //; case.
  by split=> //; [case | move=> _; exists xs', σ; rewrite hstart].
(* a call from an ongoing state: the label is kept, or the call settles *)
case: (tools_label F (call q) _ _ hD) => [hl|hs];
  first by rewrite hl hon; split=> //; case.
have [hg hfree] := (settle_model F (call q) hs _ _).1 hD.
case: (settle_label F (call q) hs _ _ hfree) => ->;
  first by rewrite hon; split=> //; case.
by split=> //; [case | move=> _; exists xs', q, σ; rewrite hstart].
Qed.

End Completion.

Arguments next_record {S K P ch πK x inp o κ} _ s.
Arguments exec_init {S K P W ch πK E s₀ w x xs} _ _.
Arguments next_active {S K P ch πK x inp o κ} _ _.
Arguments next_init_ctrl {S K P ch πK x inp o κ} _ _.
Arguments next_init_inactive {S K P ch πK x inp o κ} _ _.
Arguments completion {S K P W ch πK E} hA1 hA2 F {s₀} _ {w x xs} _.

(** ** Proposition 1, and the agent tools of §3.5.2 *)

Section Settlement.

Variables (S : Type) (K : Contract S).

(** **Proposition 1 (What settlement asks).** Let the call [c] be settlement,
[free_settle|Goal], and let the certificate establish that [free_settle] is
admissible at every compliant active state where the goal holds. Under A3, for
every view [v] and delay [n], the delayed obligation of settlement is the goal
at every active state of the window of every compliant active state with the
view [v]. *)
Theorem settle_obligation (hK : Cert K) (Goal : pred S)
    (freeD : S -> S -> Prop) (c : Call K)
    (hmodel : forall s s', D K c s s' <-> Goal s /\ freeD s s')
    (hfree : forall s, Active K s -> C K s -> Goal s -> wp freeD (C K) s)
    (n : nat) (v : V K) :
  OblN K n c v <->
    forall s s', Active K s -> Active K s' -> view K s = v -> C K s ->
      Win K n s s' -> Goal s'.
Proof.
split=> h s s' ha ha' hv hc hw.
  by have [[s'' /hmodel[]]] := h s s' ha ha' hv hc hw.
have hg := h s s' ha ha' hv hc hw.
have [[s'' hd] hall] := hfree s' ha' (win_C hK hc hw) hg.
split; first by exists s''; apply/hmodel.
by move=> t /hmodel[_ ht]; exact: hall.
Qed.

Arguments settle_obligation : clear implicits.

(** The settlement obligation (§3.5.2, Eq. settlement-obligation): with no
control step, the goal at every compliant active state with the view. *)
Theorem settle_obligation_zero (hK : Cert K) (Goal : pred S)
    (freeD : S -> S -> Prop) (c : Call K)
    (hmodel : forall s s', D K c s s' <-> Goal s /\ freeD s s')
    (hfree : forall s, Active K s -> C K s -> Goal s -> wp freeD (C K) s)
    (v : V K) :
  Obl K c v <-> forall s, Active K s -> C K s -> view K s = v -> Goal s.
Proof.
have hN := settle_obligation hK Goal freeD c hmodel hfree 0 v.
have hZ := oblN_zero c v.
split=> [/hZ.2 /hN h s ha hc hv|h]; first exact: (h s s ha ha hv hc (erefl s)).
by apply/hZ.1/hN => s s' ha _ hv hc /= <-; exact: h.
Qed.

Arguments settle_obligation_zero : clear implicits.

(** When the view determines the goal, settling is exactly the goal (§3.5.2). *)
Theorem settle_obligation_view (hK : Cert K) (Goal : pred S)
    (freeD : S -> S -> Prop) (c : Call K)
    (hmodel : forall s s', D K c s s' <-> Goal s /\ freeD s s')
    (hfree : forall s, Active K s -> C K s -> Goal s -> wp freeD (C K) s)
    (hview : forall s s', view K s = view K s' -> Goal s = Goal s')
    {s : S} :
  Active K s -> C K s -> (Obl K c (view K s) <-> Goal s).
Proof.
move=> ha hc; have hZ :=
  settle_obligation_zero hK Goal freeD c hmodel hfree (view K s).
split=> [/hZ h|hg]; first exact: h s ha hc (erefl _).
by apply/hZ => s' _ _ hv; rewrite (hview s' s hv).
Qed.

Arguments settle_obligation_view : clear implicits.

End Settlement.

Arguments settle_obligation {S K} hK Goal freeD c hmodel hfree n v.
Arguments settle_obligation_zero {S K} hK Goal freeD c hmodel hfree v.
Arguments settle_obligation_view {S K} hK Goal freeD c hmodel hfree hview
  {s} _ _.


(** **The communication tool of §3.5.2.** A tool [send (d, r)] whose model only
adds [m = (d, r)] to the record of disclosures [sent], under the clause that
disclosures stay within [Allowed], where the state space admits the updated
record: at a compliant state its admissibility is exactly [(d, r) ∈ Allowed]. *)
Theorem send_adm {S M : Type} (sent : S -> seq M) (Allowed : pred M)
    (m : M) (s : S) :
  (exists s', sent s' = m :: sent s) -> all Allowed (sent s) ->
  wp (fun s s' => sent s' = m :: sent s) (fun s => all Allowed (sent s)) s <->
    Allowed m.
Proof.
move=> [s' hs'] hc; split=> [[_ /(_ s' hs')]|hm].
  by rewrite hs' /= => /andP[].
by split=> [|s'' ->]; [exists s' | rewrite /= hm hc].
Qed.
