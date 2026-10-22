import PC2.Compliance

/-!
# Completion (§4.2): Theorem 2 and Proposition 1, and the agent tools of §3.5.2

A contract is in **standard form** (Example 1) when its label says whether it is active, its settlement
tool is `free_settle|Goal`, only control and settlement change the label, control starts the contract
only from a `Ready` state and terminates it only from a state in `End`, and settlement only settles.
Theorem 2 holds for every contract in standard form; the template of Example 1 (`PC2.Standard`) is one.
-/

namespace PC2

/-- The status of a standard contract (Example 1). -/
inductive Label where
  | pending
  | ongoing
  | settled
  | terminated
  | void
  deriving DecidableEq, Repr

variable {S : Type}

/-- **Standard form (Example 1).** The facts about a contract that Theorem 2 uses, on the models: the
label `lab` (held by the Airlock) is `ongoing` exactly on the active states; the settlement tool's model
is the goal as a precondition on `free_settle`, which can only settle; the other tools leave the label
unchanged; from `pending`, control makes the contract ongoing only from a `Ready` state and otherwise
leaves it pending or void; from `ongoing`, control keeps it ongoing, or terminates it, only from a state
in `End`. -/
structure StandardForm (K : Contract S) where
  lab : S → Label
  active_iff : ∀ s, K.Active s ↔ lab s = .ongoing
  settle : K.Name
  Goal : S → Prop
  freeD : K.Call → S → S → Prop
  settle_model : ∀ (c : K.Call), c.1 = settle → ∀ s s', K.D c s s' ↔ Goal s ∧ freeD c s s'
  settle_label : ∀ (c : K.Call), c.1 = settle → ∀ s s', freeD c s s' →
    lab s' = lab s ∨ lab s' = .settled
  tools_label : ∀ (c : K.Call), c.1 ≠ settle → ∀ s s', K.D c s s' → lab s' = lab s
  Ready : S → Prop
  End : S → Prop
  ctrl_pending : ∀ s s', lab s = .pending → K.ctrl s s' →
    (lab s' = .ongoing ∧ Ready s) ∨ lab s' = .pending ∨ (lab s' = .void ∧ ¬ Ready s)
  ctrl_ongoing : ∀ s s', lab s = .ongoing → K.ctrl s s' →
    lab s' = .ongoing ∨ (lab s' = .terminated ∧ End s)

section

variable {K : Contract S} {P W : Type} {ch : Checker P} {πK : P} {E : Effects K W}

theorem next_record {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S → Vars K P} (h : Next K ch πK x inp o κ) (s : S) : (κ s).record = s := by
  match h with
  | .init .. => rfl
  | .call .. => rfl
  | .ctrl .. => rfl
  | .ctrlAfterCall .. => rfl

/-- The only variables of an execution in the initial phase are the starting ones. -/
theorem exec_init {s₀ : S} {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)}
    (h : Exec K ch πK E s₀ w x xs) (hx : x.phase = .init) : x.record = s₀ ∧ xs = [] := by
  cases h with
  | start => exact ⟨rfl, rfl⟩
  | step σ l _ hn _ _ => exact absurd hx (next_phase hn _)

/-- An operation that Algorithm 1 invokes after initialization starts from an active state. -/
theorem next_active {x : Vars K P} {inp : Input K P} {o : Op K P} {κ : S → Vars K P}
    (h : Next K ch πK x inp o κ) (hx : x.phase ≠ .init) : K.Active x.record := by
  match h with
  | .init _ _ h' _ _ => exact absurd h' hx
  | .call _ _ _ _ _ ha _ _ _ _ => exact ha
  | .ctrl _ _ _ _ ha _ _ => exact ha
  | .ctrlAfterCall _ _ _ ha => exact ha

/-- Initialization is a control step. -/
theorem next_init_ctrl {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S → Vars K P} (h : Next K ch πK x inp o κ) (hx : x.phase = .init) : o = .ctrl := by
  match h with
  | .init .. => rfl
  | .call _ _ _ _ h' .. => exact absurd (hx.symm.trans h') (by decide)
  | .ctrl _ _ _ h' .. => exact absurd (hx.symm.trans h') (by decide)
  | .ctrlAfterCall _ _ h' _ => exact absurd (hx.symm.trans h') (by decide)

/-- Initialization starts from an inactive state. -/
theorem next_init_inactive {x : Vars K P} {inp : Input K P} {o : Op K P}
    {κ : S → Vars K P} (h : Next K ch πK x inp o κ) (hx : x.phase = .init) :
    ¬ K.Active x.record := by
  match h with
  | .init _ _ _ _ hin => exact hin
  | .call _ _ _ _ h' .. => exact absurd (hx.symm.trans h') (by decide)
  | .ctrl _ _ _ h' .. => exact absurd (hx.symm.trans h') (by decide)
  | .ctrlAfterCall _ _ h' _ => exact absurd (hx.symm.trans h') (by decide)

/-- **Theorem 2 (Completion).** Under A1 and A2, for a contract in standard form created `pending`, in
every execution of Algorithms 1–2 the label of the last reading says how the contract ended, in exactly
one way:
1. *void* (or still pending): the conditions to start did not hold, and no tool call was made;
2. *settled*: the last operation was the settlement, which started from a state where the goal held;
3. *terminated*: the last operation was a control step, which started from a state in `End`, where the
   control step found a termination condition. -/
theorem completion (hA1 : ch.Sound) (hA2 : Coverage K E) (F : StandardForm K) {s₀ : S}
    (hs₀ : F.lab s₀ = .pending) {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)}
    (hX : Exec K ch πK E s₀ w x xs) :
    ((F.lab x.record = .pending ∨ F.lab x.record = .void) → ∀ p ∈ xs, p.1 = .ctrl) ∧
    (F.lab x.record = .settled → ∃ xs' q σ, xs = xs' ++ [(.call q, σ)] ∧ q.call.1 = F.settle ∧
      F.Goal (σ.pt σ.first).2) ∧
    (F.lab x.record = .terminated → ∃ xs' σ, xs = xs' ++ [(.ctrl, σ)] ∧ F.End (σ.pt σ.first).2) := by
  cases hX with
  | start =>
    simp only [start] at *
    refine ⟨fun _ p hp => by simp at hp, fun h => ?_, fun h => ?_⟩ <;> rw [hs₀] at h <;> cases h
  | @step w' x' xs' inp o κ σ l hprev hn hfirst he =>
    obtain ⟨hI, hph, _⟩ := exec_inv hA1 hA2 hprev
    have hsafe := next_safe hA1 hI hn
    have hD : o.model x'.record (σ.pt l).2 := hA2.op hsafe.1 (he l)
    have hrec : (κ (σ.pt l).2).record = (σ.pt l).2 := next_record hn _
    have hstart : (σ.pt σ.first).2 = x'.record := by rw [hfirst]
    rw [hrec]
    by_cases hinit : x'.phase = .init
    · -- the last operation is the initialization, from `s₀`
      obtain ⟨hr₀, rfl⟩ := exec_init hprev hinit
      have ho := next_init_ctrl hn hinit
      subst ho
      have hpend : F.lab x'.record = .pending := by rw [hr₀]; exact hs₀
      have hc := F.ctrl_pending _ _ hpend hD
      refine ⟨fun _ p hp => ?_, fun h => ?_, fun h => ?_⟩
      · simp at hp; rw [hp]
      · exfalso; rcases hc with ⟨h', _⟩ | h' | ⟨h', _⟩ <;> simp [h] at h'
      · exfalso; rcases hc with ⟨h', _⟩ | h' | ⟨h', _⟩ <;> simp [h] at h'
    · -- the last operation starts from an ongoing state
      have hon : F.lab x'.record = .ongoing := (F.active_iff _).1 (next_active hn hinit)
      cases o with
      | ctrl =>
        have hc := F.ctrl_ongoing _ _ hon hD
        refine ⟨fun h => ?_, fun h => ?_, fun h => ⟨xs', σ, rfl, ?_⟩⟩
        · exfalso
          rcases hc with h' | ⟨h', _⟩ <;> rcases h with h | h <;> simp [h] at h'
        · exfalso
          rcases hc with h' | ⟨h', _⟩ <;> simp [h] at h'
        · rcases hc with h' | ⟨_, hE⟩
          · exfalso; simp [h] at h'
          · rw [hstart]; exact hE
      | call q =>
        by_cases hs : q.call.1 = F.settle
        · have hm := (F.settle_model q.call hs _ _).1 hD
          have hl := F.settle_label q.call hs _ _ hm.2
          refine ⟨fun h => ?_, fun _ => ⟨xs', q, σ, rfl, hs, ?_⟩, fun h => ?_⟩
          · exfalso
            rcases hl with h' | h' <;> rcases h with h | h <;> simp [h, hon] at h'
          · rw [hstart]; exact hm.1
          · exfalso
            rcases hl with h' | h' <;> simp [h, hon] at h'
        · have hl := F.tools_label q.call hs _ _ hD
          rw [hon] at hl
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
          · exfalso; rcases h with h | h <;> simp [h] at hl
          · exfalso; simp [h] at hl
          · exfalso; simp [h] at hl

end

/-! ## Proposition 1, and the agent tools of §3.5.2 -/

namespace Contract

variable (K : Contract S)

/-- **Proposition 1 (What settlement asks).** Let the call `c` be settlement, `free_settle|Goal`, and
let the certificate establish that `free_settle` is admissible at every compliant active state where
the goal holds. Under A3, for every view `v` and delay `n`, the delayed obligation of settlement is the
goal at every active state of the window of every compliant active state with the view `v`. -/
theorem settle_obligation (hK : K.Cert) (Goal : S → Prop) (freeD : S → S → Prop) (c : K.Call)
    (hmodel : ∀ s s', K.D c s s' ↔ Goal s ∧ freeD s s')
    (hfree : ∀ s, K.Active s → K.C s → Goal s → wp freeD K.C s) (n : Nat) (v : K.V) :
    K.OblN n c v ↔
      ∀ s s', K.Active s → K.Active s' → K.view s = v → K.C s → K.Win n s s' → Goal s' := by
  constructor
  · intro h s s' ha ha' hv hc hw
    obtain ⟨⟨s'', hd⟩, _⟩ := h s s' ha ha' hv hc hw
    exact ((hmodel _ _).1 hd).1
  · intro h s s' ha ha' hv hc hw
    have hg := h s s' ha ha' hv hc hw
    obtain ⟨⟨s'', hd⟩, hall⟩ := hfree s' ha' (K.win_C hK hc hw) hg
    exact ⟨⟨s'', (hmodel _ _).2 ⟨hg, hd⟩⟩, fun s'' hd => hall s'' ((hmodel _ _).1 hd).2⟩

/-- The settlement obligation (§3.5.2, Eq. settlement-obligation): with no control step, the goal at
every compliant active state with the view. -/
theorem settle_obligation_zero (hK : K.Cert) (Goal : S → Prop) (freeD : S → S → Prop)
    (c : K.Call) (hmodel : ∀ s s', K.D c s s' ↔ Goal s ∧ freeD s s')
    (hfree : ∀ s, K.Active s → K.C s → Goal s → wp freeD K.C s) (v : K.V) :
    K.Obl c v ↔ ∀ s, K.Active s → K.C s → K.view s = v → Goal s := by
  rw [← K.oblN_zero, K.settle_obligation hK Goal freeD c hmodel hfree 0 v]
  constructor
  · intro h s ha hc hv; exact h s s ha ha hv hc rfl
  · intro h s s' ha _ hv hc hw; cases hw; exact h s ha hc hv

/-- When the view determines the goal, settling is exactly the goal (§3.5.2). -/
theorem settle_obligation_view (hK : K.Cert) (Goal : S → Prop) (freeD : S → S → Prop)
    (c : K.Call) (hmodel : ∀ s s', K.D c s s' ↔ Goal s ∧ freeD s s')
    (hfree : ∀ s, K.Active s → K.C s → Goal s → wp freeD K.C s)
    (hview : ∀ s s', K.view s = K.view s' → (Goal s ↔ Goal s')) {s : S} (ha : K.Active s)
    (hc : K.C s) : K.Obl c (K.view s) ↔ Goal s := by
  rw [K.settle_obligation_zero hK Goal freeD c hmodel hfree]
  exact ⟨fun h => h s ha hc rfl, fun hg s' _ _ hv => (hview s' s hv).2 hg⟩

end Contract

/-- **The communication tool of §3.5.2.** A tool `send (d, r)` whose model only adds `(d, r)` to the
record of disclosures, under the clause that disclosures stay within `Allowed`, where the state space
admits the updated record: at a compliant state its admissibility is exactly `(d, r) ∈ Allowed`. -/
theorem send_adm {M : Type} (Sent : S → M → Prop) (Allowed : M → Prop) (m : M) (s : S)
    (hupd : ∃ s', ∀ y, Sent s' y ↔ Sent s y ∨ y = m) (hc : ∀ y, Sent s y → Allowed y) :
    wp (fun s s' => (∀ y, Sent s y → Sent s' y) ∧ (∀ y, Sent s' y → Sent s y ∨ y = m))
      (fun s => ∀ y, Sent s y → Allowed y) s ↔ Allowed m := by
  obtain ⟨s', hs'⟩ := hupd
  constructor
  · intro ⟨_, hall⟩
    exact hall s' ⟨fun y hy => (hs' y).2 (Or.inl hy), fun y hy => (hs' y).1 hy⟩ m
      ((hs' m).2 (Or.inr rfl))
  · intro hm
    refine ⟨⟨s', fun y hy => (hs' y).2 (Or.inl hy), fun y hy => (hs' y).1 hy⟩, ?_⟩
    intro s'' ⟨_, hsub⟩ y hy
    rcases hsub y hy with h | rfl
    · exact hc y h
    · exact hm

end PC2
