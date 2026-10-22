import PC2.World

/-!
# Capability modules (§6): Definitions 5–7, Propositions 2–4, Theorem 6

A capability module packages a world, a state, a correspondence, and tools whose effects (for reference
executions) are known, including an idle tool. Coverage and fidelity are established module by module;
Theorem 6 combines them for tools that are tensors of module tools, given compatibility of effects.

Products are taken over any index type `ι` (a module per index, `Fin n` for `n` modules), as dependent
functions; regrouping and permuting the factors is reindexing.
-/

namespace PC2

/-- **Definition 5 (Capability module).** A world, a state, a correspondence; tools over the state
with their effects, `eff l i w s w' s'` (an invocation of the tool `l` on `i` from `(w, s)` can reach
`(w', s')`, for reference executions); and the idle tool, which waits without intervening. -/
structure Module where
  W : Type
  S : Type
  ρ : W → S → Prop
  Name : Type
  tools : Name → Tool S
  eff : (l : Name) → (tools l).Inp → W → S → W → S → Prop
  idle : Name

namespace Module

variable (M : Module)

/-- Local coverage `Cov_M(T)` (Eq. local-cov). -/
def Cov (l : M.Name) : Prop :=
  ∀ i s s', (M.tools l).En i s → (∃ w w', M.eff l i w s w' s') → (M.tools l).D i s s'

/-- Local fidelity `Fid_M(T)` (Eq. local-fid). -/
def Fid (l : M.Name) : Prop :=
  ∀ i w s w' s', M.ρ w s → (M.tools l).En i s → M.eff l i w s w' s' → M.ρ w' s'

end Module

/-! ## Tensors, compatibility, and Theorem 6 -/

section Tensor

variable {ι : Type} (M : ι → Module)

/-- The tensor of one tool from each module (Eq. product-model): inputs and states componentwise, the
conjunction of the models. -/
def tensor (sel : ∀ k, (M k).Name) : Tool (∀ k, (M k).S) where
  Inp := ∀ k, ((M k).tools (sel k)).Inp
  D i s s' := ∀ k, ((M k).tools (sel k)).D (i k) (s k) (s' k)

/-- The correspondence of the product: componentwise. -/
def prodρ (w : ∀ k, (M k).W) (s : ∀ k, (M k).S) : Prop := ∀ k, (M k).ρ (w k) (s k)

/-- **Compatibility of effects** (Eq. no-coupling): each effect of the tensor, as it runs in the combined
system, projects to an effect of each component, idle components included. -/
def Compatible (sel : ∀ k, (M k).Name)
    (effT : (tensor M sel).Inp → (∀ k, (M k).W) → (∀ k, (M k).S) → (∀ k, (M k).W) →
      (∀ k, (M k).S) → Prop) : Prop :=
  ∀ i w s w' s', effT i w s w' s' → ∀ k, (M k).eff (sel k) (i k) (w k) (s k) (w' k) (s' k)

variable {M}

/-- An enabled tensor has every component enabled. -/
theorem tensor_en {sel : ∀ k, (M k).Name} {i : (tensor M sel).Inp} {s : ∀ k, (M k).S}
    (h : (tensor M sel).En i s) (k : ι) : ((M k).tools (sel k)).En (i k) (s k) :=
  let ⟨s', hs'⟩ := h; ⟨s' k, hs' k⟩

/-- **Theorem 6 (From local to global guarantees)**, coverage. -/
theorem local_to_global_cov (sel : ∀ k, (M k).Name) (effT : (tensor M sel).Inp →
    (∀ k, (M k).W) → (∀ k, (M k).S) → (∀ k, (M k).W) → (∀ k, (M k).S) → Prop)
    (hcomp : Compatible M sel effT) (hcov : ∀ k, (M k).Cov (sel k)) :
    ∀ i s s', (tensor M sel).En i s → (∃ w w', effT i w s w' s') → (tensor M sel).D i s s' :=
  fun _ _ _ hen ⟨w, w', he⟩ k => hcov k _ _ _ (tensor_en hen k) ⟨w k, w' k, hcomp _ _ _ _ _ he k⟩

/-- **Theorem 6 (From local to global guarantees)**, fidelity (the first line of A5). -/
theorem local_to_global_fid (sel : ∀ k, (M k).Name) (effT : (tensor M sel).Inp →
    (∀ k, (M k).W) → (∀ k, (M k).S) → (∀ k, (M k).W) → (∀ k, (M k).S) → Prop)
    (hcomp : Compatible M sel effT) (hfid : ∀ k, (M k).Fid (sel k)) :
    ∀ i w s w' s', prodρ M w s → (tensor M sel).En i s → effT i w s w' s' → prodρ M w' s' :=
  fun _ _ _ _ _ hρ hen he k => hfid k _ _ _ _ _ (hρ k) (tensor_en hen k) (hcomp _ _ _ _ _ he k)

end Tensor

/-- **A contract built from modules** (§6.2, "Building a contract"): its tools and its control step are
tensors of module tools, with their effects in the combined system; the contract supplies its clause,
view and inactivity test. -/
structure Composite {ι : Type} (M : ι → Module) where
  Name : Type
  sel : Name → ∀ k, (M k).Name
  effT : (l : Name) → (tensor M (sel l)).Inp → (∀ k, (M k).W) → (∀ k, (M k).S) →
    (∀ k, (M k).W) → (∀ k, (M k).S) → Prop
  selCtrl : ∀ k, (M k).Name
  ctrlInp : (tensor M selCtrl).Inp
  effCtrl : (∀ k, (M k).W) → (∀ k, (M k).S) → (∀ k, (M k).W) → (∀ k, (M k).S) → Prop

namespace Composite

variable {ι : Type} {M : ι → Module} (X : Composite M)

/-- The contract, for a clause, a view and an inactivity test on the combined state. -/
def contract (C : (∀ k, (M k).S) → Prop) (V : Type) (view : (∀ k, (M k).S) → V)
    (stop : (∀ k, (M k).S) → Bool) : Contract (∀ k, (M k).S) where
  C := C
  V := V
  view := view
  Name := X.Name
  tools l := tensor M (X.sel l)
  ctrl s s' := (tensor M X.selCtrl).D X.ctrlInp s s'
  stop := stop

/-- Its effects in the combined system. -/
def effects (C : (∀ k, (M k).S) → Prop) (V : Type) (view : (∀ k, (M k).S) → V)
    (stop : (∀ k, (M k).S) → Bool) : Effects (X.contract C V view stop) (∀ k, (M k).W) where
  call c := X.effT c.1 c.2
  ctrl := X.effCtrl

/-- **Theorem 6 for a contract built from modules.** With compatible effects, local coverage of every
module tool gives A2, and local fidelity gives the first line of A5, for the contract's tools and its
control step. -/
theorem local_to_global (C : (∀ k, (M k).S) → Prop) (V : Type) (view : (∀ k, (M k).S) → V)
    (stop : (∀ k, (M k).S) → Bool) (hcomp : ∀ l, Compatible M (X.sel l) (X.effT l))
    (hcompC : Compatible M X.selCtrl (fun i w s w' s' => i = X.ctrlInp ∧ X.effCtrl w s w' s'))
    (hcov : ∀ k (l : (M k).Name), (M k).Cov l) :
    Coverage (X.contract C V view stop) (X.effects C V view stop) where
  call c s s' hen he :=
    local_to_global_cov (X.sel c.1) (X.effT c.1) (hcomp c.1) (fun k => hcov k _) c.2 s s' hen he
  ctrl s s' hen := fun ⟨w, w', he⟩ =>
    local_to_global_cov X.selCtrl _ hcompC (fun k => hcov k _) X.ctrlInp s s' hen
      ⟨w, w', rfl, he⟩

theorem local_to_global_fidelity (C : (∀ k, (M k).S) → Prop) (V : Type)
    (view : (∀ k, (M k).S) → V) (stop : (∀ k, (M k).S) → Bool)
    (hcomp : ∀ l, Compatible M (X.sel l) (X.effT l))
    (hcompC : Compatible M X.selCtrl (fun i w s w' s' => i = X.ctrlInp ∧ X.effCtrl w s w' s'))
    (hfid : ∀ k (l : (M k).Name), (M k).Fid l) :
    (∀ (c : (X.contract C V view stop).Call) w s w' s', prodρ M w s →
        (∃ s'', (X.contract C V view stop).D c s s'') → (X.effects C V view stop).call c w s w' s' →
        prodρ M w' s') ∧
      (∀ w s w' s', prodρ M w s → (∃ s'', (X.contract C V view stop).ctrl s s'') →
        (X.effects C V view stop).ctrl w s w' s' → prodρ M w' s') :=
  ⟨fun c w s w' s' hρ hen he =>
    local_to_global_fid (X.sel c.1) (X.effT c.1) (hcomp c.1) (fun k => hfid k _) c.2 w s w' s' hρ
      hen he,
   fun w s w' s' hρ hen he =>
    local_to_global_fid X.selCtrl _ hcompC (fun k => hfid k _) X.ctrlInp w s w' s' hρ hen
      ⟨rfl, he⟩⟩

end Composite

/-! ## Restriction and extension (§6.4) -/

/-- A precondition keeps local coverage (§6.4): the restricted model is enabled only where the
original one is, and agrees with it there. -/
theorem cov_restrict {S W : Type} (T : Tool S) (Pre : T.Inp → S → Prop)
    (eff : T.Inp → W → S → W → S → Prop)
    (h : ∀ i s s', T.En i s → (∃ w w', eff i w s w' s') → T.D i s s') :
    ∀ i s s', (T.restrict Pre).En i s → (∃ w w', eff i w s w' s') → (T.restrict Pre).D i s s' :=
  fun i s s' hen he =>
    let ⟨hp, hen'⟩ := (T.en_restrict Pre i s).1 hen
    ⟨hp, h i s s' hen' he⟩

/-- A precondition keeps local fidelity (§6.4). -/
theorem fid_restrict {S W : Type} (T : Tool S) (Pre : T.Inp → S → Prop)
    (eff : T.Inp → W → S → W → S → Prop) (ρ : W → S → Prop)
    (h : ∀ i w s w' s', ρ w s → T.En i s → eff i w s w' s' → ρ w' s') :
    ∀ i w s w' s', ρ w s → (T.restrict Pre).En i s → eff i w s w' s' → ρ w' s' :=
  fun i w s w' s' hρ hen he => h i w s w' s' hρ ((T.en_restrict Pre i s).1 hen).2 he

/-- **Definition 7 (Extension)**: new state `Z`, a correspondence `ρ'` for it, and new tools on the full
state; the retained tools keep `z` unchanged (Eq. extension-model). -/
def Module.ext (M : Module) (Z : Type) (ρ' : M.W → M.S → Z → Prop) (N : Type)
    (new : N → Tool (M.S × Z))
    (effNew : (n : N) → (new n).Inp → M.W → M.S × Z → M.W → M.S × Z → Prop)
    (effOld : (l : M.Name) → (M.tools l).Inp → M.W → M.S × Z → M.W → M.S × Z → Prop) : Module where
  W := M.W
  S := M.S × Z
  ρ w sz := M.ρ w sz.1 ∧ ρ' w sz.1 sz.2
  Name := M.Name ⊕ N
  tools
    | .inl l => ⟨(M.tools l).Inp, fun i sz sz' => (M.tools l).D i sz.1 sz'.1 ∧ sz'.2 = sz.2⟩
    | .inr n => new n
  eff
    | .inl l => effOld l
    | .inr n => effNew n
  idle := .inl M.idle

/-- **Checking an extension** (§6.4), for the retained tools: if their effects in the extended system
project within their original effects and leave `z` unchanged, their coverage proofs establish the
lifted models; if moreover they preserve the added correspondence, their fidelity proofs give fidelity
in the extended module. -/
theorem ext_retained (M : Module) (Z : Type) (ρ' : M.W → M.S → Z → Prop) (N : Type)
    (new : N → Tool (M.S × Z))
    (effNew : (n : N) → (new n).Inp → M.W → M.S × Z → M.W → M.S × Z → Prop)
    (effOld : (l : M.Name) → (M.tools l).Inp → M.W → M.S × Z → M.W → M.S × Z → Prop)
    (l : M.Name)
    (hproj : ∀ i w sz w' sz', effOld l i w sz w' sz' → M.eff l i w sz.1 w' sz'.1 ∧ sz'.2 = sz.2) :
    (M.Cov l → (M.ext Z ρ' N new effNew effOld).Cov (.inl l)) ∧
    (M.Fid l → (∀ i w sz w' sz', M.ρ w sz.1 → ρ' w sz.1 sz.2 → (M.tools l).En i sz.1 →
        effOld l i w sz w' sz' → ρ' w' sz'.1 sz'.2) →
      (M.ext Z ρ' N new effNew effOld).Fid (.inl l)) := by
  refine ⟨fun hcov i sz sz' hen ⟨w, w', he⟩ => ?_, fun hfid hρ' i w sz w' sz' hρ hen he => ?_⟩
  · obtain ⟨s'', hs''⟩ := hen
    obtain ⟨he₁, hz⟩ := hproj i w sz w' sz' he
    exact ⟨hcov i sz.1 sz'.1 ⟨s''.1, hs''.1⟩ ⟨w, w', he₁⟩, hz⟩
  · obtain ⟨s'', hs''⟩ := hen
    obtain ⟨he₁, _⟩ := hproj i w sz w' sz' he
    exact ⟨hfid i w sz.1 w' sz'.1 hρ.1 ⟨s''.1, hs''.1⟩ he₁,
      hρ' i w sz w' sz' hρ.1 hρ.2 ⟨s''.1, hs''.1⟩ he⟩

/-! ## Three capability constructions (§6.3) -/

section Custody

variable {Instr Wc : Type} (J : Wc → Instr → Prop)

/-- **The custody module** (Eq. custody-module): the register of payment instructions, `issue j`, and
idle; every submitted instruction is registered. -/
def custody (effIssue : Instr → Wc → (Instr → Prop) → Wc → (Instr → Prop) → Prop)
    (effIdle : Wc → (Instr → Prop) → Wc → (Instr → Prop) → Prop) : Module where
  W := Wc
  S := Instr → Prop
  ρ w s := ∀ j, J w j → s j
  Name := Bool
  tools
    | true => ⟨Instr, fun j s s' => s' = s ∨ s' = fun y => s y ∨ y = j⟩
    | false => ⟨Unit, fun _ s s' => s' = s⟩
  eff
    | true => effIssue
    | false => fun _ => effIdle
  idle := false

/-- **Proposition 2 (Custody).** Under (H1) only `issue j` changes the register, by adding `j`, and idle
leaves it unchanged; and (H2) an instruction is submitted only by `issue`, once it is registered: both
tools, idle included, are covered and faithful. -/
theorem custody_guarantees
    (effIssue : Instr → Wc → (Instr → Prop) → Wc → (Instr → Prop) → Prop)
    (effIdle : Wc → (Instr → Prop) → Wc → (Instr → Prop) → Prop)
    (H1 : (∀ j w s w' s', effIssue j w s w' s' → s' = s ∨ s' = fun y => s y ∨ y = j) ∧
      (∀ w s w' s', effIdle w s w' s' → s' = s))
    (H2 : (∀ j w s w' s', effIssue j w s w' s' → ∀ y, J w' y → J w y ∨ (y = j ∧ s' y)) ∧
      (∀ w s w' s', effIdle w s w' s' → ∀ y, J w' y → J w y)) :
    ∀ l, (custody J effIssue effIdle).Cov l ∧ (custody J effIssue effIdle).Fid l := by
  intro l
  cases l with
  | true =>
    refine ⟨fun j s s' _ ⟨w, w', he⟩ => H1.1 j w s w' s' he, ?_⟩
    intro j w s w' s' hρ _ he y hy
    have hgrow : ∀ y, s y → s' y := by
      rcases H1.1 j w s w' s' he with rfl | rfl
      · exact fun _ h => h
      · exact fun _ h => Or.inl h
    rcases H2.1 j w s w' s' he y hy with h | ⟨_, h⟩
    · exact hgrow y (hρ y h)
    · exact h
  | false =>
    refine ⟨fun _ s s' _ ⟨w, w', he⟩ => H1.2 w s w' s' he, ?_⟩
    intro _ w s w' s' hρ _ he y hy
    rw [H1.2 w s w' s' he]
    exact hρ y (H2.2 w s w' s' he y hy)

end Custody

section Interface

variable {Req Resp Wf : Type} (request : Resp → Req) (Spec : Resp → Prop) (H : Wf → Resp → Prop)

/-- **The formal-interface module** (Eq. interface-module): a log of response events, `query q`, and
idle; every recorded response was issued by the service and is permitted by its specification. -/
def interface (effQuery : Req → Wf → (Resp → Prop) → Wf → (Resp → Prop) → Prop)
    (effIdle : Wf → (Resp → Prop) → Wf → (Resp → Prop) → Prop) : Module where
  W := Wf
  S := Resp → Prop
  ρ w s := ∀ e, s e → H w e ∧ Spec e
  Name := Bool
  tools
    | true => ⟨Req, fun q s s' => s' = s ∨ ∃ e, request e = q ∧ Spec e ∧ s' = fun y => s y ∨ y = e⟩
    | false => ⟨Unit, fun _ s s' => s' = s⟩
  eff
    | true => effQuery
    | false => fun _ => effIdle
  idle := false

/-- **Proposition 3 (Formal interface).** If the history retains its events, (F1) every response issued
by the service satisfies the specification, and (F2) only `query q` changes the log, leaving it
unchanged or appending one event issued for `q`, while idle leaves it unchanged: both tools, idle
included, are covered and faithful. -/
theorem interface_guarantees
    (effQuery : Req → Wf → (Resp → Prop) → Wf → (Resp → Prop) → Prop)
    (effIdle : Wf → (Resp → Prop) → Wf → (Resp → Prop) → Prop)
    (retain : (∀ q w s w' s', effQuery q w s w' s' → ∀ e, H w e → H w' e) ∧
      (∀ w s w' s', effIdle w s w' s' → ∀ e, H w e → H w' e))
    (F1 : ∀ w e, H w e → Spec e)
    (F2 : (∀ q w s w' s', effQuery q w s w' s' →
        s' = s ∨ ∃ e, request e = q ∧ H w' e ∧ s' = fun y => s y ∨ y = e) ∧
      (∀ w s w' s', effIdle w s w' s' → s' = s)) :
    ∀ l, (interface request Spec H effQuery effIdle).Cov l ∧
      (interface request Spec H effQuery effIdle).Fid l := by
  intro l
  cases l with
  | true =>
    refine ⟨fun q s s' _ ⟨w, w', he⟩ => ?_, fun q w s w' s' hρ _ he e hs' => ?_⟩
    · rcases F2.1 q w s w' s' he with h | ⟨e, hq, hH, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, hq, F1 w' e hH, h⟩
    · rcases F2.1 q w s w' s' he with rfl | ⟨e', _, hH, rfl⟩
      · exact ⟨retain.1 q w s' w' s' he e (hρ e hs').1, (hρ e hs').2⟩
      · rcases hs' with h | rfl
        · exact ⟨retain.1 q w s w' _ he e (hρ e h).1, (hρ e h).2⟩
        · exact ⟨hH, F1 w' e hH⟩
  | false =>
    refine ⟨fun _ s s' _ ⟨w, w', he⟩ => F2.2 w s w' s' he, fun _ w s w' s' hρ _ he e hs' => ?_⟩
    rw [F2.2 w s w' s' he] at hs'
    exact ⟨retain.2 w s w' s' he e (hρ e hs').1, (hρ e hs').2⟩

end Interface

section Invariant

/-- **Proposition 4 (Domain invariant).** For a module whose correspondence is `s = π(w) ∧ K(w)`
(Eq. shared-model-transition): if (M1) the state at every instant is `π` of the world, and (M2) every
enabled tool, idle included, preserves `K`, then every tool is faithful; and adequacy follows from
`K(w) ∧ C(π(w)) → Safe(w)` (Eq. shared-model-adequacy). -/
theorem domain_invariant (M : Module) (π : M.W → M.S) (Kinv : M.W → Prop)
    (hρ : ∀ w s, M.ρ w s ↔ s = π w ∧ Kinv w)
    (M1 : ∀ l i w s w' s', M.eff l i w s w' s' → s' = π w')
    (M2 : ∀ l i w s w' s', (M.tools l).En i s → Kinv w → M.eff l i w s w' s' → Kinv w') :
    (∀ l, M.Fid l) ∧ ∀ (C : M.S → Prop) (Safe : M.W → Prop),
      (∀ w, Kinv w → C (π w) → Safe w) → ∀ w s, M.ρ w s → C s → Safe w := by
  refine ⟨fun l i w s w' s' h hen he => ?_, fun C Safe hadq w s h hc => ?_⟩
  · obtain ⟨_, hK⟩ := (hρ w s).1 h
    exact (hρ w' s').2 ⟨M1 l i w s w' s' he, M2 l i w s w' s' hen hK he⟩
  · obtain ⟨rfl, hK⟩ := (hρ w s).1 h
    exact hadq w hK hc

end Invariant

end PC2
