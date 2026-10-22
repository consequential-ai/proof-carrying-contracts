import PC2.Isolation
import PC2.Standard

/-!
# The guarantees of PC2 (§5.4): Theorem 5

For every agent, under A1, A4 (the execution is one of Algorithms 1–2), A6, A7 as stated in §5.2, and A2
and A5 for the reference executions only. A3 is checked by the Airlock before it starts, so it is not a
hypothesis. A7 gives the stepwise isolation of App. G (`System.A7.isolation`), hence Lemma 2.
-/

namespace PC2

variable {S : Type}

section

variable {K : Contract S} {P W : Type} {ch : Checker P} {πK : P} {ρ : W → S → Prop}

/-- **Theorem 5 (1), anytime safety, for every agent.** -/
theorem guarantees (sys : System K W) (hA1 : ch.Sound) (hA2 : Coverage K sys.refEffects)
    (hA5 : Fidelity K sys.refEffects ρ) {Safe : W → Prop} (hA6 : Adequacy K ρ Safe)
    (α : sys.Agent) (hA7 : sys.A7 α) {s₀ : S} {xs : List (Op K P × Segment W S)}
    (hX : Execution K ch πK (sys.effects α) s₀ xs) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst),
      (0 < j ∨ K.Active (xs[j].2.pt τ).2) → Safe (xs[j].2.pt τ).1 :=
  world_safety hA1 (sys.coverage_of_ref α hA7.isolation hA2)
    (sys.fidelity_of_ref α hA7.isolation hA5) hA6 hX

/-- **Theorem 5 (2)–(3), for every agent and a contract in standard form created pending.** If the
contract is settled, the last operation was the settlement, which started at an instant where the goal
held in the world; if it is terminated, the last operation was a control step that found a termination
condition (its starting state is in `End`). Theorem 2 (1) gives the third way, void. -/
theorem guarantees_standard (sys : System K W) (hA1 : ch.Sound) (hA2 : Coverage K sys.refEffects)
    (hA5 : Fidelity K sys.refEffects ρ) (F : StandardForm K) {GoalW : W → Prop}
    (hA6 : GoalAdequacy ρ F.Goal GoalW) (α : sys.Agent) (hA7 : sys.A7 α) {s₀ : S}
    (hs₀ : F.lab s₀ = .pending) {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)}
    (hX : Exec K ch πK (sys.effects α) s₀ w x xs) :
    (F.lab x.record = .settled → ∃ xs' q σ, xs = xs' ++ [(.call q, σ)] ∧ q.call.1 = F.settle ∧
      GoalW (σ.pt σ.first).1) ∧
    (F.lab x.record = .terminated → ∃ xs' σ, xs = xs' ++ [(.ctrl, σ)] ∧ F.End (σ.pt σ.first).2) := by
  have hA2' := sys.coverage_of_ref α hA7.isolation hA2
  have hA5' := sys.fidelity_of_ref α hA7.isolation hA5
  have hT2 := completion hA1 hA2' F hs₀ hX
  refine ⟨fun hset => ?_, hT2.2.2⟩
  obtain ⟨xs', q, σ, rfl, hs, _⟩ := hT2.2.1 hset
  refine ⟨xs', q, σ, rfl, hs, ?_⟩
  have hj : xs'.length < (xs' ++ [(Op.call q, σ)]).length := by simp
  have := completion_in_world hA1 hA2' hA5' F hA6 (.returned hX) xs'.length hj q (by simp) hs
  exact of_getElem_append_length (P := fun (a : Op K P × Segment W S) => GoalW (a.2.pt a.2.first).1) this

/-- **Theorem 5 (4), the deadline, for every agent.** For a clause that keeps the clock within `d`
while the contract is active, and a correspondence in which the state's clock does not lag behind the
world's time: at no instant of an execution whose world time is past `d` is the contract active.
Settlement or termination has begun by `d`. -/
theorem guarantees_deadline (sys : System K W) (hA1 : ch.Sound) (hA2 : Coverage K sys.refEffects)
    (hA5 : Fidelity K sys.refEffects ρ) (α : sys.Agent) (hA7 : sys.A7 α) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK (sys.effects α) s₀ xs)
    (now : W → Nat) (time : S → Nat) (d : Nat) (hclause : ∀ s, K.Active s → K.C s → time s ≤ d)
    (hclock : ∀ w s, ρ w s → now w ≤ time s) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst), d < now (xs[j].2.pt τ).1 →
      ¬ K.Active (xs[j].2.pt τ).2 :=
  deadline hA1 (sys.coverage_of_ref α hA7.isolation hA2) (sys.fidelity_of_ref α hA7.isolation hA5)
    hX now time d hclause hclock

end

/-- The standard contract keeps its clock within the deadline while it is active. -/
theorem Standard.Spec.deadline_clause {X : Type} (sp : Standard.Spec X) (s : Standard.St X)
    (ha : sp.contract.Active s) (hc : sp.contract.C s) : s.t ≤ sp.d :=
  ((sp.C_iff ((sp.active_iff s).1 ha)).1 hc).2

end PC2
