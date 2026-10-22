/-!
# The formal core (§3): tools, contracts, obligations, the certificate

Definitions 1–4 of the paper, admissibility (Eqs. 1–3) as a weakest precondition (App. A), the
precondition construction (§3.5.2), and A3 as the statement of the certificate the Airlock checks
before it starts (Algorithm 1, line 2).

A predicate on `X` is a function `X → Prop`, a relation a function `X → Y → Prop`; a decidable test is
a function to `Bool`.
-/

namespace PC2

/-- The relational weakest precondition (App. A): from `s`, the relation `R` admits some outcome, and
every outcome satisfies `Q`. -/
def wp {S : Type} (R : S → S → Prop) (Q : S → Prop) (s : S) : Prop :=
  (∃ s', R s s') ∧ ∀ s', R s s' → Q s'

/-! ## Tools (§3.1) -/

/-- **Definition 1 (Tool).** An input space `I_T` and a transition model `D_T`: `D i s s'` holds for
every state `s'` the model admits during an invocation on `i` from `s`, its initial, intermediate and
final states, outside changes included. The execution routine `exec_T` is not a mathematical object:
what it does enters through the effects of a deployment (`PC2.Effects`). -/
structure Tool (S : Type) where
  Inp : Type
  D : Inp → S → S → Prop

namespace Tool

variable {S : Type} (T : Tool S)

/-- Enabledness `Ξ_T(i,s)` (Eq. 2): the model admits some state. -/
def En (i : T.Inp) (s : S) : Prop := ∃ s', T.D i s s'

/-- Daemonic control `Θ_T(i,s)` (Eq. 1): every state the model admits satisfies `C`. -/
def Dem (C : S → Prop) (i : T.Inp) (s : S) : Prop := ∀ s', T.D i s s' → C s'

/-- Admissibility `𝒜_T(i,s)` (Eq. 3), the weakest precondition of the model for `C`. -/
def Adm (C : S → Prop) (i : T.Inp) (s : S) : Prop := wp (T.D i) C s

/-- `𝒜_T = Ξ_T ∧ Θ_T`, by definition. -/
theorem adm_iff (C : S → Prop) (i : T.Inp) (s : S) : T.Adm C i s ↔ T.En i s ∧ T.Dem C i s :=
  Iff.rfl

/-- **The precondition construction** `T|_Pre` (§3.5.2): same input and routine, the model restricted
to the starting states where `Pre` holds. -/
def restrict (Pre : T.Inp → S → Prop) : Tool S where
  Inp := T.Inp
  D i s s' := Pre i s ∧ T.D i s s'

/-- `Ξ_{T|Pre}(i,s) ⟺ Pre(i,s) ∧ Ξ_T(i,s)` (§3.5.2). -/
theorem en_restrict (Pre : T.Inp → S → Prop) (i : T.Inp) (s : S) :
    (T.restrict Pre).En i s ↔ Pre i s ∧ T.En i s :=
  ⟨fun ⟨s', hp, hd⟩ => ⟨hp, s', hd⟩, fun ⟨hp, s', hd⟩ => ⟨s', hp, hd⟩⟩

/-- Under a precondition, admissibility is the precondition and the original admissibility; this is
the obligation of Eq. (precondition-obligation) at each state (§3.5.2). -/
theorem adm_restrict (C : S → Prop) (Pre : T.Inp → S → Prop) (i : T.Inp) (s : S) :
    (T.restrict Pre).Adm C i s ↔ Pre i s ∧ T.Adm C i s :=
  ⟨fun ⟨⟨s', hp, hd⟩, hall⟩ => ⟨hp, ⟨s', hd⟩, fun s' hd => hall s' ⟨hp, hd⟩⟩,
   fun ⟨hp, ⟨s', hd⟩, hall⟩ => ⟨⟨s', hp, hd⟩, fun s' ⟨_, hd⟩ => hall s' hd⟩⟩

end Tool

/-! ## Contracts (§3.2) -/

/-- **Definition 2 (Contract)** `𝒦 = (Σ, C, View, 𝒯, ctrl, stop)`, with `Σ` the type `S`: the clause
`C`, the view, the tools available to the agent (`tools`, by name), the model of the control tool
(`ctrl`, which has no input and is reserved for the Airlock), and the decidable inactivity test
`stop`. A contract fixes no initial state. -/
structure Contract (S : Type) where
  C : S → Prop
  V : Type
  view : S → V
  Name : Type
  tools : Name → Tool S
  ctrl : S → S → Prop
  stop : S → Bool

namespace Contract

variable {S : Type} (K : Contract S)

/-- The active states `Σ_act`; the others are the inactive states `Σ_stop`. -/
def Active (s : S) : Prop := K.stop s = false

/-- A call: a tool of the contract and an input of it. -/
abbrev Call := (l : K.Name) × (K.tools l).Inp

/-- The model of a call. -/
def D (c : K.Call) : S → S → Prop := (K.tools c.1).D c.2

/-- Admissibility of a call at a state (Eq. 3). -/
def Adm (c : K.Call) (s : S) : Prop := wp (K.D c) K.C s

/-! ## Obligations (§3.3) -/

/-- **Definition 3 (Obligation)** `Obl_T(i,v)`: the call is admissible at every compliant active
state with the view `v`. -/
def Obl (c : K.Call) (v : K.V) : Prop :=
  ∀ s, K.Active s → K.view s = v → K.C s → K.Adm c s

/-- The window `D^{≤n}_ctrl` (Eq. delayed-control): at most `n` control steps, through active states.
As in the paper it is cumulative: a window contains the shorter ones. -/
def Win : Nat → S → S → Prop
  | 0, s, s' => s = s'
  | n + 1, s, s' => Win n s s' ∨ ∃ u, K.Active u ∧ Win n s u ∧ K.ctrl u s'

/-- **Definition 4 (Delayed obligation)** `Obl^{≤n}_T(i,v)`: the call is admissible at every active
state in the window of every compliant active state with the view `v`. -/
def OblN (n : Nat) (c : K.Call) (v : K.V) : Prop :=
  ∀ s s', K.Active s → K.Active s' → K.view s = v → K.C s → K.Win n s s' → K.Adm c s'

/-- **A3 (Initialization and control)**, as the statement of the certificate `π_𝒦` that the Airlock
checks before it starts (Algorithm 1, line 2). -/
structure Cert : Prop where
  /-- The controller line: from a compliant active state, control is admissible. -/
  controller : ∀ s, K.Active s → K.C s → wp K.ctrl K.C s
  /-- The initializer line: from an inactive state, control makes the contract active only in `C`. -/
  initializer : ∀ s s', ¬ K.Active s → K.Active s' → K.ctrl s s' → K.C s'
  /-- Control is enabled at every inactive state. -/
  enabled : ∀ s, ¬ K.Active s → ∃ s', K.ctrl s s'

/-- With no control step, the delayed obligation is the obligation (§3.3). -/
theorem oblN_zero (c : K.Call) (v : K.V) : K.OblN 0 c v ↔ K.Obl c v := by
  constructor
  · intro h s ha hv hc
    exact h s s ha ha hv hc rfl
  · intro h s s' ha _ hv hc hw
    cases hw
    exact h s ha hv hc

/-- A longer window contains a shorter one. -/
theorem win_mono {m n : Nat} (hmn : m ≤ n) {s s' : S} (hw : K.Win m s s') : K.Win n s s' := by
  induction hmn with
  | refl => exact hw
  | step _ ih => exact Or.inl ih

/-- One more control step, from an active state, extends a window. -/
theorem win_snoc {n : Nat} {s u s' : S} (hw : K.Win n s u) (hu : K.Active u) (hc : K.ctrl u s') :
    K.Win (n + 1) s s' :=
  Or.inr ⟨u, hu, hw, hc⟩

/-- Under A3, the states of a window of a compliant state comply. -/
theorem win_C (hK : K.Cert) : ∀ {n : Nat} {s s' : S}, K.C s → K.Win n s s' → K.C s'
  | 0, _, _, hc, hw => by cases hw; exact hc
  | _ + 1, _, _, hc, .inl hw => win_C hK hc hw
  | _ + 1, _, _, hc, .inr ⟨u, hu, hw, hc'⟩ => (hK.controller u hu (win_C hK hc hw)).2 _ hc'

/-- The delayed obligation is antitone in the allowance. -/
theorem oblN_mono {m n : Nat} (hmn : m ≤ n) {c : K.Call} {v : K.V} (h : K.OblN n c v) :
    K.OblN m c v :=
  fun s s' ha ha' hv hc hw => h s s' ha ha' hv hc (K.win_mono hmn hw)

end Contract

end PC2
