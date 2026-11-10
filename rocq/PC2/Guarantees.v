(** * The guarantees of PC2 (§5.4): Theorem 5

For every agent, under A1, A4 (the execution is one of Algorithms 1–2), A6, A7
as stated in §5.2, and A2 and A5 for the reference executions only. A3 is
checked by the Airlock before it starts, so it is not a hypothesis. A7 gives the
stepwise isolation of App. G ([System.A7_isolation]), hence Lemma 2. That the
standard contract keeps its clock within the deadline while it is active, as
Theorem 5 (4) asks of the clause, is [Standard.Spec.deadline_clause]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution Compliance Completion World
  Isolation.

Unset Printing Implicit Defensive.

Import Contract StandardForm.

Section Guarantees.

Context {S : Type} {K : Contract S} {P W : Type} {ch : Checker P} {πK : P}
  {ρ : W -> S -> Prop}.

(** **Theorem 5 (1), anytime safety, for every agent.** *)
Theorem guarantees (sys : System.t K W) (hA1 : Checker.Sound ch)
    (hA2 : Coverage K (System.refEffects sys))
    (hA5 : Fidelity K (System.refEffects sys) ρ)
    {Safe : W -> Prop} (hA6 : Adequacy K ρ Safe)
    (α : System.Agent sys) (hA7 : System.A7 sys α)
    {s₀ : S} {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK (System.effects sys α) s₀ xs ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    (0 < j \/ Active K (pt p.2 τ).2) -> Safe (pt p.2 τ).1.
Proof.
exact: (world_safety hA1 (System.coverage_of_A7 sys α hA7 hA2)
  (System.fidelity_of_A7 sys α hA7 hA5) hA6).
Qed.

(** **Theorem 5 (2)–(3), for every agent and a contract in standard form created
pending.** If the contract is settled, the last operation was the settlement,
which started at an instant where the goal held in the world; if it is
terminated, the last operation was a control step that found a termination
condition (its starting state is in [End]). Theorem 2 (1) gives the third way,
void. *)
Theorem guarantees_standard (sys : System.t K W) (hA1 : Checker.Sound ch)
    (hA2 : Coverage K (System.refEffects sys))
    (hA5 : Fidelity K (System.refEffects sys) ρ)
    (F : StandardForm K) {GoalW : W -> Prop}
    (hA6 : GoalAdequacy ρ (Goal F) GoalW)
    (α : System.Agent sys) (hA7 : System.A7 sys α) {s₀ : S} :
  lab F s₀ = Pending ->
  forall {w : W} {x : Vars K P} {xs : seq (Op K P * Segment W S)},
  Exec K ch πK (System.effects sys α) s₀ w x xs ->
  (lab F (record x) = Settled ->
    exists xs' q σ, [/\ xs = rcons xs' (OpCall q, σ),
      projT1 (call q) = settle F & GoalW (pt σ (first σ)).1]) /\
  (lab F (record x) = Terminated ->
    exists xs' σ, xs = rcons xs' (OpCtrl, σ) /\ Ends F (pt σ (first σ)).2).
Proof.
move=> hs₀ w x xs hX.
have hA2' := System.coverage_of_A7 sys α hA7 hA2.
have hA5' := System.fidelity_of_A7 sys α hA7 hA5.
have [_ hset hterm] := completion hA1 hA2' F hs₀ hX.
split=> // /hset[xs' [q [σ [hxs hs _]]]].
exists xs', q, σ; split=> //; subst xs.
exact: (completion_in_world hA1 hA2' hA5' F hA6 (returned hX) (size xs') _
  (onth_rcons_size xs' (OpCall q, σ)) q erefl hs).
Qed.

(** **Theorem 5 (4), the deadline, for every agent.** For a clause that keeps
the clock within [d] while the contract is active, and a correspondence in which
the state's clock does not lag behind the world's time: at no instant of an
execution whose world time is past [d] is the contract active. Settlement or
termination has begun by [d]. *)
Theorem guarantees_deadline (sys : System.t K W) (hA1 : Checker.Sound ch)
    (hA2 : Coverage K (System.refEffects sys))
    (hA5 : Fidelity K (System.refEffects sys) ρ)
    (α : System.Agent sys) (hA7 : System.A7 sys α) {s₀ : S}
    {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK (System.effects sys α) s₀ xs ->
  forall (now : W -> nat) (time : S -> nat) (d : nat),
  (forall s, Active K s -> C K s -> time s <= d) ->
  (forall w s, ρ w s -> now w <= time s) ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    d < now (pt p.2 τ).1 -> stop K (pt p.2 τ).2.
Proof.
exact: (deadline hA1 (System.coverage_of_A7 sys α hA7 hA2)
  (System.fidelity_of_A7 sys α hA7 hA5)).
Qed.

End Guarantees.
