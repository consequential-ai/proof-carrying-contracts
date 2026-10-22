import PC2.Completion

/-!
# From compliance to safety (§5.1): A5, A6, Theorem 3, Corollary 4, and the deadline

A world `w` and a state `s` correspond, `ρ(w, s)`, when `s` is a valid description of `w`. Fidelity (A5)
asks every enabled operation to preserve the correspondence at every instant, and control to establish
it when it starts the contract; adequacy (A6) asks every world described by a compliant state to be
safe, and every world described by a state where the goal holds to satisfy the goal in the world.
-/

namespace PC2

variable {S : Type}

section

variable (K : Contract S) {W : Type} (E : Effects K W) (ρ : W → S → Prop)

/-- **A5 (Fidelity).** Every enabled operation preserves the correspondence at every instant, and
control, when it starts the contract, establishes it. -/
structure Fidelity : Prop where
  call : ∀ (c : K.Call) (w : W) (s : S) (w' : W) (s' : S),
    ρ w s → (∃ s'', K.D c s s'') → E.call c w s w' s' → ρ w' s'
  ctrl : ∀ (w : W) (s : S) (w' : W) (s' : S),
    ρ w s → (∃ s'', K.ctrl s s'') → E.ctrl w s w' s' → ρ w' s'
  init : ∀ (w : W) (s : S) (w' : W) (s' : S),
    ¬ K.Active s → K.Active s' → E.ctrl w s w' s' → ρ w' s'

/-- **A6 (Adequacy)**, first part: a world described by a compliant state is safe. -/
def Adequacy (Safe : W → Prop) : Prop := ∀ w s, ρ w s → K.C s → Safe w

/-- **A6 (Adequacy)**, second part: a world described by a state where the goal holds satisfies the goal
in the world. -/
def GoalAdequacy (Goal : S → Prop) (GoalW : W → Prop) : Prop := ∀ w s, ρ w s → Goal s → GoalW w

end

section

variable {K : Contract S} {P W : Type} {ch : Checker P} {πK : P} {E : Effects K W}
  {ρ : W → S → Prop}

theorem Fidelity.op (h : Fidelity K E ρ) {o : Op K P} {w w' : W} {s s' : S} (hρ : ρ w s)
    (hen : ∃ s'', o.model s s'') (he : E.op o w s w' s') : ρ w' s' := by
  cases o with
  | ctrl => exact h.ctrl w s w' s' hρ hen he
  | call q => exact h.call q.call w s w' s' hρ hen he

variable (ρ) in
/-- The correspondence at every instant of an operation, from the start of the contract. -/
def SegFaithful (j : Nat) (σ : Segment W S) : Prop :=
  ∀ τ : σ.Inst, (0 < j ∨ K.Active (σ.pt τ).2) → ρ (σ.pt τ).1 (σ.pt τ).2

/-- An operation that Algorithm 1 invokes from a world its record describes (after initialization):
under A1, A2 and A5, the correspondence holds at each of its instants, from the start of the
contract. -/
theorem segment_faithful (hA1 : ch.Sound) (hA5 : Fidelity K E ρ) {w : W} {x : Vars K P}
    {inp : Input K P} {o : Op K P} {κ : S → Vars K P} {j : Nat} (hI : Inv K ch x)
    (hj : x.phase = .init ↔ j = 0) (hρ : x.phase ≠ .init → K.Active x.record → ρ w x.record)
    (h : Next K ch πK x inp o κ) (σ : Segment W S)
    (he : ∀ τ, E.op o w x.record (σ.pt τ).1 (σ.pt τ).2) : SegFaithful (K := K) ρ j σ := by
  intro τ hor
  by_cases hinit : x.phase = .init
  · have hj0 : j = 0 := hj.1 hinit
    have ha : K.Active (σ.pt τ).2 := by
      rcases hor with h' | h'
      · omega
      · exact h'
    have ho := next_init_ctrl h hinit
    have he' := he τ
    rw [ho] at he'
    exact hA5.init _ _ _ _ (next_init_inactive h hinit) ha he'
  · exact hA5.op (hρ hinit (next_active h hinit)) (next_safe hA1 hI h).1 (he τ)

/-- Every execution keeps the correspondence, under A1, A2 and A5. -/
theorem exec_world (hA1 : ch.Sound) (hA2 : Coverage K E) (hA5 : Fidelity K E ρ) {s₀ : S} {w : W}
    {x : Vars K P} {xs : List (Op K P × Segment W S)} (h : Exec K ch πK E s₀ w x xs) :
    (x.phase ≠ .init → K.Active x.record → ρ w x.record) ∧
      ∀ j (hj : j < xs.length), SegFaithful (K := K) ρ j xs[j].2 := by
  induction h with
  | start => exact ⟨fun h => absurd rfl h, fun j h => by simp at h⟩
  | @step w x xs inp o κ σ l hprev hn _ he ih =>
    obtain ⟨hI, hph, _⟩ := exec_inv hA1 hA2 hprev
    have hj : x.phase = .init ↔ xs.length = 0 := by rw [hph]; simp
    have hseg := segment_faithful hA1 hA5 hI hj ih.1 hn σ he
    refine ⟨fun _ ha => ?_,
      forall_append (P := fun j (a : Op K P × Segment W S) => SegFaithful (K := K) ρ j a.2) ih.2 hseg⟩
    rw [next_record hn] at ha ⊢
    by_cases hinit : x.phase = .init
    · exact hseg l (Or.inr ha)
    · exact hseg l (Or.inl (by
        have : xs ≠ [] := fun h' => hinit (hph.2 h')
        exact List.length_pos_iff.2 this))

/-- The world and the compliance facts of every operation of an execution, including one still
running. -/
theorem execution_world (hA1 : ch.Sound) (hA2 : Coverage K E) (hA5 : Fidelity K E ρ) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) :
    ∀ j (hj : j < xs.length), SegFaithful (K := K) ρ j xs[j].2 := by
  cases hX with
  | returned hx => exact (exec_world hA1 hA2 hA5 hx).2
  | @running w x xs inp o κ σ hx hn _ he =>
    obtain ⟨hI, hph, _⟩ := exec_inv hA1 hA2 hx
    have hj : x.phase = .init ↔ xs.length = 0 := by rw [hph]; simp
    exact forall_append (P := fun j (a : Op K P × Segment W S) => SegFaithful (K := K) ρ j a.2)
      (exec_world hA1 hA2 hA5 hx).2
      (segment_faithful hA1 hA5 hI hj (exec_world hA1 hA2 hA5 hx).1 hn σ he)

/-- **Theorem 3 (World safety).** Under A1, A2, A5 and A6, for any sequence of requests and proposed
proofs, every execution of Algorithms 1–2 (A4) is safe in the world at every instant of every operation
from the start of the contract, closing included, and throughout an operation that never returns. -/
theorem world_safety (hA1 : ch.Sound) (hA2 : Coverage K E) (hA5 : Fidelity K E ρ)
    {Safe : W → Prop} (hA6 : Adequacy K ρ Safe) {s₀ : S} {xs : List (Op K P × Segment W S)}
    (hX : Execution K ch πK E s₀ xs) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst),
      (0 < j ∨ K.Active (xs[j].2.pt τ).2) → Safe (xs[j].2.pt τ).1 :=
  fun j h τ hor => hA6 _ _ (execution_world hA1 hA2 hA5 hX j h τ hor)
    (anytime_compliance hA1 hA2 hX j h τ hor)

/-- Where each operation of an execution starts: from variables that satisfy the invariant, with the
operation chosen by Algorithm 1, at the world and record where the previous one ended. -/
theorem execution_starts (hA1 : ch.Sound) (hA2 : Coverage K E) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) :
    ∀ j (hj : j < xs.length), ∃ (w : W) (x : Vars K P) (inp : Input K P)
      (κ : S → Vars K P), Inv K ch x ∧ (x.phase = .init ↔ j = 0) ∧
      Next K ch πK x inp xs[j].1 κ ∧ xs[j].2.pt xs[j].2.first = (w, x.record) := by
  have key : ∀ {w : W} {x : Vars K P} {ys : List (Op K P × Segment W S)},
      Exec K ch πK E s₀ w x ys → ∀ j (hj : j < ys.length), ∃ (w : W) (x : Vars K P)
        (inp : Input K P) (κ : S → Vars K P), Inv K ch x ∧ (x.phase = .init ↔ j = 0) ∧
        Next K ch πK x inp ys[j].1 κ ∧ ys[j].2.pt ys[j].2.first = (w, x.record) := by
    intro w x ys h
    induction h with
    | start => intro j h; simp at h
    | @step w x xs inp o κ σ l hprev hn hfirst _ ih =>
      obtain ⟨hI, hph, _⟩ := exec_inv hA1 hA2 hprev
      refine forall_append (P := fun j (a : Op K P × Segment W S) => ∃ (w : W) (x : Vars K P) (inp : Input K P)
        (κ : S → Vars K P), Inv K ch x ∧ (x.phase = .init ↔ j = 0) ∧
        Next K ch πK x inp a.1 κ ∧ a.2.pt a.2.first = (w, x.record)) ih ?_
      exact ⟨w, x, inp, κ, hI, by rw [hph]; simp, hn, hfirst⟩
  cases hX with
  | returned hx => exact key hx
  | @running w x xs inp o κ σ hx hn hfirst _ =>
    obtain ⟨hI, hph, _⟩ := exec_inv hA1 hA2 hx
    refine forall_append (P := fun j (a : Op K P × Segment W S) => ∃ (w : W) (x : Vars K P) (inp : Input K P)
      (κ : S → Vars K P), Inv K ch x ∧ (x.phase = .init ↔ j = 0) ∧
      Next K ch πK x inp a.1 κ ∧ a.2.pt a.2.first = (w, x.record)) (key hx) ?_
    exact ⟨w, x, inp, κ, hI, by rw [hph]; simp, hn, hfirst⟩

/-- **Corollary 4 (Completion in the world).** Under the assumptions of Theorem 2, with A5 and the goal
part of A6: every invocation of the settlement routine starts at an instant where the goal holds in the
world. -/
theorem completion_in_world (hA1 : ch.Sound) (hA2 : Coverage K E) (hA5 : Fidelity K E ρ)
    (F : StandardForm K) {GoalW : W → Prop} (hA6 : GoalAdequacy ρ F.Goal GoalW) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) :
    ∀ j (h : j < xs.length) (q : Request K P), xs[j].1 = .call q → q.call.1 = F.settle →
      GoalW (xs[j].2.pt xs[j].2.first).1 := by
  intro j h q hop hs
  obtain ⟨w, x, inp, κ, hI, hph, hn, hfirst⟩ := execution_starts hA1 hA2 hX j h
  rw [hop] at hn
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · have := next_init_ctrl hn (hph.2 h0); cases this
    · exact h0
  have hρ := execution_world hA1 hA2 hA5 hX j h xs[j].2.first (Or.inl hj0)
  obtain ⟨⟨s'', hd⟩, _⟩ := next_safe hA1 hI hn
  have hG := ((F.settle_model q.call hs _ _).1 hd).1
  rw [hfirst] at hρ ⊢
  exact hA6 _ _ hρ hG

/-- **The deadline, in the world.** For a clause that keeps the clock within `d` while the contract is
active, and a correspondence in which the state's clock does not lag behind the world's time: at no
instant of an execution whose world time is past `d` is the contract active (Theorem 5 (4)). -/
theorem deadline (hA1 : ch.Sound) (hA2 : Coverage K E) (hA5 : Fidelity K E ρ) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) (now : W → Nat)
    (time : S → Nat) (d : Nat) (hclause : ∀ s, K.Active s → K.C s → time s ≤ d)
    (hclock : ∀ w s, ρ w s → now w ≤ time s) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst), d < now (xs[j].2.pt τ).1 →
      ¬ K.Active (xs[j].2.pt τ).2 := by
  intro j h τ hd ha
  have hC := anytime_compliance hA1 hA2 hX j h τ (Or.inr ha)
  have hρ := execution_world hA1 hA2 hA5 hX j h τ (Or.inr ha)
  have := hclause _ ha hC
  have := hclock _ _ hρ
  omega

end

end PC2
