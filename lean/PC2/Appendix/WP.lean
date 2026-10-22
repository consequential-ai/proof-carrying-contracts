import PC2.World

/-!
# Appendix A: the obligation as a weakest precondition

What the agent knows, `K_n(v)`; Eq. (A.1); gates; Proposition A.1, the most permissive safe gate; and the
policy-engine example.
-/

namespace PC2

namespace Contract

variable {S : Type} (K : Contract S)

/-- **What the agent knows** (App. A): the states it cannot rule out for a call that may start after up
to `n` control steps from a view `v`. -/
def Kn (n : Nat) (v : K.V) (s' : S) : Prop :=
  K.Active s' ∧ ∃ s, K.Active s ∧ K.view s = v ∧ K.C s ∧ K.Win n s s'

/-- **Eq. (A.1)**: the delayed obligation is the weakest precondition of the call for `C` at every state
the agent cannot rule out. -/
theorem oblN_wp (n : Nat) (c : K.Call) (v : K.V) :
    K.OblN n c v ↔ ∀ s', K.Kn n v s' → wp (K.D c) K.C s' :=
  ⟨fun h s' ⟨ha', s, ha, hv, hc, hw⟩ => h s s' ha ha' hv hc hw,
   fun h s s' ha ha' hv hc hw => h s' ⟨ha', s, ha, hv, hc, hw⟩⟩

/-- A gate decides, from a request and the view it is based on, whether the call may run; it is
**safe** if every call it admits is admissible at every state from which it may start. -/
def SafeGate (G : K.Call → Nat → K.V → Prop) : Prop :=
  ∀ c n v, G c n v → ∀ s', K.Kn n v s' → K.Adm c s'

/-- **Proposition A.1 (The most permissive safe gate).** The obligation is a safe gate, and every safe
gate implies it. -/
theorem most_permissive_gate :
    K.SafeGate (fun c n v => K.OblN n c v) ∧
      ∀ G, K.SafeGate G → ∀ c n v, G c n v → K.OblN n c v :=
  ⟨fun c n v h => (K.oblN_wp n c v).1 h,
   fun _ hG c n v hg => (K.oblN_wp n c v).2 (hG c n v hg)⟩

/-- **Proposition A.1, second part.** A decidable safe gate that admitted every call whose obligation
holds would decide the obligation: where the obligations are undecidable, every decidable safe gate
rejects some call whose obligation holds. -/
theorem decidable_gate (g : K.Call → Nat → K.V → Bool)
    (hsafe : K.SafeGate (fun c n v => g c n v = true))
    (hall : ∀ c n v, K.OblN n c v → g c n v = true) :
    ∀ c n v, K.OblN n c v ↔ g c n v = true :=
  fun c n v => ⟨hall c n v, (K.most_permissive_gate.2 _ hsafe c n v)⟩

end Contract

/-- **The policy-engine example** (App. A): a rule that caps each of three nights at 600 keeps a budget
of 2000, and rejects a first night at 900 followed by two at 500, which keep the budget too. -/
theorem policy_engine_example :
    (∀ a b c : Nat, a ≤ 600 → b ≤ 600 → c ≤ 600 → a + b + c ≤ 2000) ∧ ¬ (900 ≤ 600) ∧
      900 + 500 + 500 ≤ 2000 :=
  ⟨fun _ _ _ _ _ _ => by omega, by decide, by decide⟩

end PC2
