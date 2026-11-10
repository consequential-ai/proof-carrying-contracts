(** * From compliance to safety (§5.1): A5, A6, Theorem 3, Corollary 4, and the
deadline

A world [w] and a state [s] correspond, [ρ(w, s)], when [s] is a valid
description of [w]. Fidelity (A5) asks every enabled operation to preserve the
correspondence at every instant, and control to establish it when it starts the
contract; adequacy (A6) asks every world described by a compliant state to be
safe, and every world described by a state where the goal holds to satisfy the
goal in the world. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution Compliance Completion.

Unset Printing Implicit Defensive.

Import Contract StandardForm.

(** **A5 (Fidelity).** Every enabled operation preserves the correspondence at
every instant, and control, when it starts the contract, establishes it. *)
Record Fidelity {S : Type} (K : Contract S) {W : Type} (E : Effects K W)
    (ρ : W -> S -> Prop) : Prop := {
  fid_call : forall (c : Call K) (w : W) (s : S) (w' : W) (s' : S),
    ρ w s -> (exists s'', D K c s s'') ->
    Effects.ecall E c w s w' s' -> ρ w' s';
  fid_ctrl : forall (w : W) (s : S) (w' : W) (s' : S),
    ρ w s -> (exists s'', ctrl K s s'') -> Effects.ectrl E w s w' s' -> ρ w' s';
  fid_init : forall (w : W) (s : S) (w' : W) (s' : S),
    stop K s -> Active K s' -> Effects.ectrl E w s w' s' -> ρ w' s';
}.

Arguments fid_call {S K W E ρ} _ c w s w' s' _ _ _.
Arguments fid_ctrl {S K W E ρ} _ w s w' s' _ _ _.
Arguments fid_init {S K W E ρ} _ w s w' s' _ _ _.

(** **A6 (Adequacy)**, first part: a world described by a compliant state is
safe. *)
Definition Adequacy {S : Type} (K : Contract S) {W : Type} (ρ : W -> S -> Prop)
    (Safe : W -> Prop) : Prop :=
  forall w s, ρ w s -> C K s -> Safe w.

(** **A6 (Adequacy)**, second part: a world described by a state where the goal
holds satisfies the goal in the world. *)
Definition GoalAdequacy {S W : Type} (ρ : W -> S -> Prop) (Goal : S -> Prop)
    (GoalW : W -> Prop) : Prop :=
  forall w s, ρ w s -> Goal s -> GoalW w.

Section World.

Context {S : Type} {K : Contract S} {P W : Type} {ch : Checker P} {πK : P}
  {E : Effects K W} {ρ : W -> S -> Prop}.

Lemma fidelity_op (h : Fidelity K E ρ) {o : Op K P} {w w' : W} {s s' : S} :
  ρ w s -> (exists s'', model o s s'') -> Effects.op E o w s w' s' -> ρ w' s'.
Proof.
by case: o => [|q];
  [exact: fid_ctrl h w s w' s' | exact: fid_call h (call q) w s w' s'].
Qed.

(** The correspondence at every instant of an operation, from the start of the
contract. *)
Definition SegFaithful (j : nat) (σ : Segment W S) : Prop :=
  forall τ : Inst σ, (0 < j \/ Active K (pt σ τ).2) -> ρ (pt σ τ).1 (pt σ τ).2.

(** An operation that Algorithm 1 invokes from a world its record describes
(after initialization): under A1, A2 and A5, the correspondence holds at each of
its instants, from the start of the contract. *)
Lemma segment_faithful (hA1 : Checker.Sound ch) (hA5 : Fidelity K E ρ)
    {w : W} {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S -> Vars K P} {j : nat} :
  Inv K ch x -> (phase x = Init <-> j = 0) ->
  (phase x <> Init -> Active K (record x) -> ρ w (record x)) ->
  Next K ch πK x inp o κ -> forall σ : Segment W S,
  (forall τ, Effects.op E o w (record x) (pt σ τ).1 (pt σ τ).2) ->
  SegFaithful j σ.
Proof.
move=> hI hj hρ h σ he τ hor.
case: (eqVneq (phase x) Init) => [hinit|/eqP hne].
  have ha : Active K (pt σ τ).2 by case: hor => //; rewrite (hj.1 hinit).
  have ho := next_init_ctrl h hinit; subst o.
  exact: (fid_init hA5 _ _ _ _ (next_init_inactive h hinit) ha (he τ)).
exact: (fidelity_op hA5 (hρ hne (next_active h hne))
  (next_safe hA1 hI h).1 (he τ)).
Qed.

Lemma phase_size {x : Vars K P} {xs : seq (Op K P * Segment W S)} :
  (phase x = Init <-> xs = [::]) -> (phase x = Init <-> size xs = 0).
Proof.
by move=> hph; split=> [/hph.1 -> //|/size0nil /hph.2].
Qed.

(** Every execution keeps the correspondence, under A1, A2 and A5. *)
Lemma exec_world (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (hA5 : Fidelity K E ρ) {s₀ : S} {w : W} {x : Vars K P}
    {xs : seq (Op K P * Segment W S)} :
  Exec K ch πK E s₀ w x xs ->
  (phase x <> Init -> Active K (record x) -> ρ w (record x)) /\
    forall j p, onth xs j = Some p -> SegFaithful j p.2.
Proof.
elim=> [w₀|{}w {}x {}xs inp o κ σ l hprev [ih1 ih2] hn _ he].
  by split=> [h|j p]; [case: h | rewrite onth0n].
have [hI hph _] := exec_inv hA1 hA2 hprev.
have hseg := segment_faithful hA1 hA5 hI (phase_size hph) ih1 hn σ he.
split; last by apply: (onth_rcons_all (fun j p => SegFaithful j p.2) ih2).
by move=> _; rewrite (next_record hn) => ha; exact: hseg l (or_intror ha).
Qed.

(** The correspondence at every instant of every operation of an execution,
including one still running. *)
Lemma execution_world (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (hA5 : Fidelity K E ρ) {s₀ : S} {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall j p, onth xs j = Some p -> SegFaithful j p.2.
Proof.
case=> [w x {}xs hx|w x {}xs inp o κ σ hx hn _ he];
  first exact: (exec_world hA1 hA2 hA5 hx).2.
have [hI hph _] := exec_inv hA1 hA2 hx.
have [hρ hall] := exec_world hA1 hA2 hA5 hx.
apply: (onth_rcons_all (fun j p => SegFaithful j p.2) hall).
exact: (segment_faithful hA1 hA5 hI (phase_size hph) hρ hn σ he).
Qed.

(** **Theorem 3 (World safety).** Under A1, A2, A5 and A6, for any sequence of
requests and proposed proofs, every execution of Algorithms 1–2 (A4) is safe in
the world at every instant of every operation from the start of the contract,
closing included, and throughout an operation that never returns. *)
Theorem world_safety (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (hA5 : Fidelity K E ρ) {Safe : W -> Prop} (hA6 : Adequacy K ρ Safe)
    {s₀ : S} {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    (0 < j \/ Active K (pt p.2 τ).2) -> Safe (pt p.2 τ).1.
Proof.
move=> hX j p hp τ hor.
exact: hA6 _ _ (execution_world hA1 hA2 hA5 hX j p hp τ hor)
  (anytime_compliance hA1 hA2 hX j p hp τ hor).
Qed.

(** Where each operation of an execution starts: from variables that satisfy the
invariant, with the operation chosen by Algorithm 1, at the world and record
where the previous one ended. *)
Lemma execution_starts (hA1 : Checker.Sound ch) (hA2 : Coverage K E) {s₀ : S}
    {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs -> forall j p, onth xs j = Some p ->
    exists (w : W) (x : Vars K P) (inp : Input K P) (κ : S -> Vars K P),
      [/\ Inv K ch x, phase x = Init <-> j = 0, Next K ch πK x inp p.1 κ &
        pt p.2 (first p.2) = (w, record x)].
Proof.
pose Q j (p : Op K P * Segment W S) :=
  exists (w : W) (x : Vars K P) (inp : Input K P) (κ : S -> Vars K P),
    [/\ Inv K ch x, phase x = Init <-> j = 0, Next K ch πK x inp p.1 κ &
      pt p.2 (first p.2) = (w, record x)].
(* The operation appended by a step of an execution starts where its [Q]
   says. *)
have last_op w x ys inp o κ σ :
    Exec K ch πK E s₀ w x ys -> Next K ch πK x inp o κ ->
    pt σ (first σ) = (w, record x) -> Q (size ys) (o, σ).
  move=> hx hn hfirst; have [hI hph _] := exec_inv hA1 hA2 hx.
  by exists w, x, inp, κ; split=> //; exact: phase_size hph.
have key w x ys :
    Exec K ch πK E s₀ w x ys -> forall j p, onth ys j = Some p -> Q j p.
  elim=> [w₀ j p|{}w {}x {}ys inp o κ σ l hprev ih hn hfirst _];
    first by rewrite onth0n.
  exact: onth_rcons_all ih (last_op _ _ _ _ _ _ _ hprev hn hfirst).
case=> [w x {}xs hx|w x {}xs inp o κ σ hx hn hfirst _]; first exact: key hx.
exact: onth_rcons_all (key _ _ _ hx) (last_op _ _ _ _ _ _ _ hx hn hfirst).
Qed.

(** **Corollary 4 (Completion in the world).** Under the assumptions of Theorem
2, with A5 and the goal part of A6: every invocation of the settlement routine
starts at an instant where the goal holds in the world. *)
Theorem completion_in_world (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (hA5 : Fidelity K E ρ) (F : StandardForm K) {GoalW : W -> Prop}
    (hA6 : GoalAdequacy ρ (Goal F) GoalW) {s₀ : S}
    {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall j p, onth xs j = Some p -> forall q : Request K P, p.1 = OpCall q ->
    projT1 (call q) = settle F -> GoalW (pt p.2 (first p.2)).1.
Proof.
move=> hX j p hp q hop hs.
have [w [x [inp [κ [hI hph hn hfirst]]]]] := execution_starts hA1 hA2 hX j p hp.
rewrite hop in hn.
have hj0 : 0 < j.
  case: j hph hp => [|//] hph _.
  by have := next_init_ctrl hn (hph.2 erefl).
have hρ := execution_world hA1 hA2 hA5 hX j p hp (first p.2) (or_introl hj0).
have [[s'' hd] _] := next_safe hA1 hI hn.
have hG := ((settle_model F (call q) hs _ _).1 hd).1.
by move: hρ; rewrite hfirst /= => hρ; exact: hA6 _ _ hρ hG.
Qed.

(** **The deadline, in the world.** For a clause that keeps the clock within [d]
while the contract is active, and a correspondence in which the state's clock
does not lag behind the world's time: at no instant of an execution whose world
time is past [d] is the contract active (Theorem 5 (4)). *)
Theorem deadline (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    (hA5 : Fidelity K E ρ) {s₀ : S} {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall (now : W -> nat) (time : S -> nat) (d : nat),
  (forall s, Active K s -> C K s -> time s <= d) ->
  (forall w s, ρ w s -> now w <= time s) ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    d < now (pt p.2 τ).1 -> stop K (pt p.2 τ).2.
Proof.
move=> hX now time d hclause hclock j p hp τ hd; apply/negPn/negP => ha.
have hC := anytime_compliance hA1 hA2 hX j p hp τ (or_intror ha).
have hρ := execution_world hA1 hA2 hA5 hX j p hp τ (or_intror ha).
have := leq_trans (hclock _ _ hρ) (hclause _ ha hC).
by rewrite leqNgt hd.
Qed.

End World.

Arguments SegFaithful {S} K {W} ρ j σ.
Arguments fidelity_op {S K P W E ρ} h {o w w' s s'} _ _ _.
