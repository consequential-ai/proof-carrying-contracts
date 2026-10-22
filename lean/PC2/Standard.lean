import PC2.Completion

/-!
# The standard contract (Example 1)

The template of Example 1, with a deadline. A state is `(x, t, ℓ)`: the task part, the time as the
clock gives it, and the label. The clause is `(B(x) ∧ t ≤ d) ∨ ℓ ≠ ongoing`, the view `(View(x), t, ℓ)`.

The agent's tools are the task tools, whose models keep the label and let time advance within a timeout,
and settlement, `free_settle|Goal`. The control step follows §3.5.1, closing first: from `pending` it
starts the contract if `Ready` holds and otherwise leaves it void; from `ongoing` it idles for one
period, unless idling could pass the deadline or a termination condition of the task holds, and then it
terminates. Settlement and termination both close the contract when they start; the payment or the
refund then runs with the contract closed. No reserve of time is needed (§3.5.1).

Proved here, once for every contract built on the template: A3 (`cert`), standard form
(`standardForm`), what settlement asks (`settle_obligation`), and the reductions of the agent's
obligations used by the examples.
-/

namespace PC2

namespace Standard

/-- The state of a standard contract: the task part, the time as the clock gives it, the label. -/
structure St (X : Type) where
  x : X
  t : Nat
  ℓ : Label

/-- A task tool: its input, what it may do to the task part (outside changes included), and its
timeout. -/
structure Task (X : Type) where
  Inp : Type
  Dx : Inp → X → X → Prop
  dur : Inp → Nat

/-- What a standard contract is made of. -/
structure Spec (X : Type) where
  /-- The view of the task part. -/
  VX : Type
  viewX : X → VX
  /-- The business constraints, the goal, the deadline. -/
  B : X → Prop
  Goal : X → Prop
  d : Nat
  /-- The task tools. -/
  N : Type
  tasks : N → Task X
  /-- What releasing the escrow does to the task part. -/
  pay : X → X → Prop
  /-- Initialization: where control may start the contract (a decidable test), what starting does,
  and how long it takes; what not starting does. -/
  Ready : X → Nat → Bool
  initX : X → X → Prop
  initDur : Nat
  voidX : X → X → Prop
  /-- Outside changes to the task part while control waits, and the idle period. -/
  out : X → X → Prop
  period : Nat
  /-- The task's own termination conditions (a decidable test), and what refunding does. -/
  endX : X → Bool
  refund : X → X → Prop

/-- The names of a standard contract's tools. -/
inductive Name (N : Type) where
  | task (l : N)
  | settle

variable {X : Type}

namespace Spec

variable (sp : Spec X)

/-- The tool of a task: the label is kept, and time advances within the timeout. -/
def taskTool (T : Task X) : Tool (St X) where
  Inp := T.Inp
  D i s s' := s'.ℓ = s.ℓ ∧ s.t ≤ s'.t ∧ s'.t ≤ s.t + T.dur i ∧ T.Dx i s.x s'.x

/-- `free_settle`: the contract closes as settled when settlement starts, then the escrow is
released. -/
def freeSettle : Tool (St X) where
  Inp := Unit
  D _ s s' := s' = s ∨ (s'.ℓ = .settled ∧ sp.pay s.x s'.x)

/-- Settlement, `free_settle|Goal` (§3.5.2). -/
def settleTool : Tool (St X) := sp.freeSettle.restrict (fun _ s => sp.Goal s.x)

/-- Where control must act: idling one more period could pass the deadline, or a termination condition
of the task holds (`Act`, §3.5.1). With no fix, `End = Act`. -/
def Act (s : St X) : Bool := decide (sp.d < s.t + sp.period) || sp.endX s.x

/-- **The control step** (§3.5.1), deciding on the state it starts from, closing first. -/
def ctrl (s s' : St X) : Prop :=
  match s.ℓ with
  | .pending =>
    if sp.Ready s.x s.t then
      (s'.ℓ = .pending ∧ s'.x = s.x) ∨ (s'.ℓ = .ongoing ∧ sp.initX s.x s'.x ∧ s'.t ≤ s.t + sp.initDur)
    else s' = s ∨ (s'.ℓ = .void ∧ sp.voidX s.x s'.x)
  | .ongoing =>
    if sp.Act s then s' = s ∨ (s'.ℓ = .terminated ∧ sp.refund s.x s'.x)
    else s'.ℓ = .ongoing ∧ s.t ≤ s'.t ∧ s'.t ≤ s.t + sp.period ∧ sp.out s.x s'.x
  | _ => s' = s

theorem ctrl_pending {s s' : St X} (h : s.ℓ = .pending) :
    sp.ctrl s s' = if sp.Ready s.x s.t then
      (s'.ℓ = .pending ∧ s'.x = s.x) ∨ (s'.ℓ = .ongoing ∧ sp.initX s.x s'.x ∧ s'.t ≤ s.t + sp.initDur)
      else s' = s ∨ (s'.ℓ = .void ∧ sp.voidX s.x s'.x) := by
  unfold ctrl; rw [h]

theorem ctrl_ongoing {s s' : St X} (h : s.ℓ = .ongoing) :
    sp.ctrl s s' = if sp.Act s then s' = s ∨ (s'.ℓ = .terminated ∧ sp.refund s.x s'.x)
      else s'.ℓ = .ongoing ∧ s.t ≤ s'.t ∧ s'.t ≤ s.t + sp.period ∧ sp.out s.x s'.x := by
  unfold ctrl; rw [h]

theorem ctrl_closed {s s' : St X} (h : s.ℓ = .settled ∨ s.ℓ = .terminated ∨ s.ℓ = .void) :
    sp.ctrl s s' = (s' = s) := by
  unfold ctrl; rcases h with h | h | h <;> rw [h]

/-- **Example 1, the standard contract**, with a deadline. -/
def contract : Contract (St X) where
  C s := (sp.B s.x ∧ s.t ≤ sp.d) ∨ s.ℓ ≠ .ongoing
  V := sp.VX × Nat × Label
  view s := (sp.viewX s.x, s.t, s.ℓ)
  Name := Name sp.N
  tools
    | .task l => taskTool (sp.tasks l)
    | .settle => sp.settleTool
  ctrl := sp.ctrl
  stop s := s.ℓ != .ongoing

theorem active_iff (s : St X) : sp.contract.Active s ↔ s.ℓ = .ongoing := by
  show (s.ℓ != .ongoing) = false ↔ s.ℓ = .ongoing
  cases h : s.ℓ <;> simp

theorem C_iff {s : St X} (h : s.ℓ = .ongoing) : sp.contract.C s ↔ sp.B s.x ∧ s.t ≤ sp.d := by
  show (sp.B s.x ∧ s.t ≤ sp.d) ∨ s.ℓ ≠ .ongoing ↔ _
  simp [h]

/-- The design obligations of the template: starting from `Ready` lands in the clause, and outside
changes while waiting keep the business constraints (and may change nothing). -/
structure Design : Prop where
  init_ok : ∀ x t x' t', sp.Ready x t = true → sp.initX x x' → t' ≤ t + sp.initDur →
    sp.B x' ∧ t' ≤ sp.d
  out_refl : ∀ x, sp.out x x
  out_B : ∀ x x', sp.B x → sp.out x x' → sp.B x'

/-- **A3 for the standard contract**, once for every contract built on the template. No reserve of
time: where idling could pass the deadline, control closes the contract at once. -/
theorem cert (hD : sp.Design) : sp.contract.Cert where
  controller s ha hc := by
    have hℓ := (sp.active_iff s).1 ha
    obtain ⟨hB, ht⟩ := (sp.C_iff hℓ).1 hc
    show (∃ s', sp.ctrl s s') ∧ ∀ s', sp.ctrl s s' → sp.contract.C s'
    simp only [sp.ctrl_ongoing hℓ]
    by_cases hact : sp.Act s = true
    · simp only [hact, ite_true]
      refine ⟨⟨s, Or.inl rfl⟩, fun s' hs' => ?_⟩
      rcases hs' with rfl | ⟨hl, _⟩
      · exact hc
      · exact Or.inr (by rw [hl]; decide)
    · have hact' : sp.Act s = false := by simpa using hact
      have htp : s.t + sp.period ≤ sp.d := by
        simp only [Act, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hact'
        omega
      simp only [hact', Bool.false_eq_true, ite_false]
      refine ⟨⟨s, hℓ, Nat.le_refl _, Nat.le_add_right _ _, hD.out_refl _⟩, fun s' hs' => ?_⟩
      obtain ⟨hl, _, ht', ho⟩ := hs'
      exact Or.inl ⟨hD.out_B _ _ hB ho, by omega⟩
  initializer s s' hin ha' hs' := by
    have hℓ' := (sp.active_iff s').1 ha'
    have hℓ : s.ℓ ≠ .ongoing := fun h => hin ((sp.active_iff s).2 h)
    change sp.ctrl s s' at hs'
    cases hs₀ : s.ℓ with
    | pending =>
      rw [sp.ctrl_pending hs₀] at hs'
      by_cases hr : sp.Ready s.x s.t = true
      · simp only [hr, ite_true] at hs'
        rcases hs' with ⟨hl, _⟩ | ⟨_, hi, ht⟩
        · rw [hl] at hℓ'; cases hℓ'
        · exact Or.inl (hD.init_ok _ _ _ _ hr hi ht)
      · simp only [hr, Bool.false_eq_true, ite_false] at hs'
        rcases hs' with rfl | ⟨hl, _⟩
        · exact absurd ha' hin
        · rw [hl] at hℓ'; cases hℓ'
    | ongoing => exact absurd hs₀ hℓ
    | settled => rw [sp.ctrl_closed (Or.inl hs₀)] at hs'; subst hs'; exact absurd ha' hin
    | terminated => rw [sp.ctrl_closed (Or.inr (Or.inl hs₀))] at hs'; subst hs'; exact absurd ha' hin
    | void => rw [sp.ctrl_closed (Or.inr (Or.inr hs₀))] at hs'; subst hs'; exact absurd ha' hin
  enabled s hin := by
    have hℓ : s.ℓ ≠ .ongoing := fun h => hin ((sp.active_iff s).2 h)
    show ∃ s', sp.ctrl s s'
    cases hs₀ : s.ℓ with
    | pending =>
      simp only [sp.ctrl_pending hs₀]
      by_cases hr : sp.Ready s.x s.t = true
      · simp only [hr, ite_true]; exact ⟨s, Or.inl ⟨hs₀, rfl⟩⟩
      · simp only [hr, Bool.false_eq_true, ite_false]; exact ⟨s, Or.inl rfl⟩
    | ongoing => exact absurd hs₀ hℓ
    | settled => exact ⟨s, by rw [sp.ctrl_closed (Or.inl hs₀)]⟩
    | terminated => exact ⟨s, by rw [sp.ctrl_closed (Or.inr (Or.inl hs₀))]⟩
    | void => exact ⟨s, by rw [sp.ctrl_closed (Or.inr (Or.inr hs₀))]⟩

/-- The model of a call of the standard contract, by its name. -/
theorem D_task (l : sp.N) (i : (sp.tasks l).Inp) (s s' : St X) :
    sp.contract.D ⟨.task l, i⟩ s s' ↔
      s'.ℓ = s.ℓ ∧ s.t ≤ s'.t ∧ s'.t ≤ s.t + (sp.tasks l).dur i ∧ (sp.tasks l).Dx i s.x s'.x :=
  Iff.rfl

theorem D_settle (i : Unit) (s s' : St X) :
    sp.contract.D ⟨.settle, i⟩ s s' ↔
      sp.Goal s.x ∧ (s' = s ∨ (s'.ℓ = .settled ∧ sp.pay s.x s'.x)) :=
  Iff.rfl

/-- **The standard contract is in standard form.** -/
def standardForm : StandardForm sp.contract where
  lab s := s.ℓ
  active_iff := sp.active_iff
  settle := .settle
  Goal s := sp.Goal s.x
  freeD _ s s' := s' = s ∨ (s'.ℓ = .settled ∧ sp.pay s.x s'.x)
  settle_model c hc s s' := by
    obtain ⟨l, i⟩ := c
    simp only at hc; subst hc
    exact sp.D_settle i s s'
  settle_label c _ s s' h := by
    rcases h with rfl | ⟨hl, _⟩
    · exact Or.inl rfl
    · exact Or.inr hl
  tools_label c hc s s' hd := by
    obtain ⟨l, i⟩ := c
    cases l with
    | task l => exact ((sp.D_task l i s s').1 hd).1
    | settle => exact absurd rfl hc
  Ready s := sp.Ready s.x s.t = true
  End s := sp.Act s = true
  ctrl_pending s s' hp hs := by
    change sp.ctrl s s' at hs
    rw [sp.ctrl_pending hp] at hs
    by_cases hr : sp.Ready s.x s.t = true
    · simp only [hr, ite_true] at hs
      rcases hs with ⟨hl, _⟩ | ⟨hl, _⟩
      · exact Or.inr (Or.inl hl)
      · exact Or.inl ⟨hl, hr⟩
    · simp only [hr, Bool.false_eq_true, ite_false] at hs
      rcases hs with rfl | ⟨hl, _⟩
      · exact Or.inr (Or.inl hp)
      · exact Or.inr (Or.inr ⟨hl, hr⟩)
  ctrl_ongoing s s' ho hs := by
    change sp.ctrl s s' at hs
    rw [sp.ctrl_ongoing ho] at hs
    by_cases hact : sp.Act s = true
    · simp only [hact, ite_true] at hs
      rcases hs with rfl | ⟨hl, _⟩
      · exact Or.inl ho
      · exact Or.inr ⟨hl, hact⟩
    · simp only [hact, Bool.false_eq_true, ite_false] at hs
      exact Or.inl hs.1

/-- **Proposition 1 for the standard contract**: settling asks exactly the goal over the window. Since
settlement closes the contract when it starts, `free_settle` is admissible at every compliant active
state, deadline included. -/
theorem settle_obligation (hD : sp.Design) (n : Nat) (v : sp.contract.V) :
    sp.contract.OblN n ⟨.settle, ()⟩ v ↔
      ∀ s s', sp.contract.Active s → sp.contract.Active s' → sp.contract.view s = v →
        sp.contract.C s → sp.contract.Win n s s' → sp.Goal s'.x := by
  refine sp.contract.settle_obligation (sp.cert hD) (fun s => sp.Goal s.x)
    (fun s s' => s' = s ∨ (s'.ℓ = .settled ∧ sp.pay s.x s'.x)) ⟨.settle, ()⟩
    (fun s s' => sp.D_settle () s s') ?_ n v
  intro s _ hc _
  refine ⟨⟨s, Or.inl rfl⟩, fun s' hs' => ?_⟩
  rcases hs' with rfl | ⟨hl, _⟩
  · exact hc
  · exact Or.inr (by rw [hl]; decide)

/-- Outside changes over any number of idle periods. -/
inductive OutStar : X → X → Prop
  | refl (x : X) : OutStar x x
  | step {x y z : X} : OutStar x y → sp.out y z → OutStar x z

/-- The window of an ongoing state of the standard contract: at most `n` idle periods, through ongoing
states. -/
theorem win_bound {n : Nat} {s s' : St X} (hw : sp.contract.Win n s s')
    (ha' : s'.ℓ = .ongoing) :
    s.ℓ = .ongoing ∧ s.t ≤ s'.t ∧ s'.t ≤ s.t + n * sp.period ∧ sp.OutStar s.x s'.x := by
  induction n generalizing s' with
  | zero => cases hw; exact ⟨ha', Nat.le_refl _, by simp, .refl _⟩
  | succ n ih =>
    have hmul : (n + 1) * sp.period = n * sp.period + sp.period := Nat.succ_mul n sp.period
    rcases hw with hw | ⟨u, hu, hw, hc⟩
    · obtain ⟨h1, h2, h3, h4⟩ := ih hw ha'
      exact ⟨h1, h2, by omega, h4⟩
    · have huℓ := (sp.active_iff u).1 hu
      obtain ⟨h1, h2, h3, h4⟩ := ih hw huℓ
      change sp.ctrl u s' at hc
      rw [sp.ctrl_ongoing huℓ] at hc
      by_cases hact : sp.Act u = true
      · simp only [hact, ite_true] at hc
        rcases hc with rfl | ⟨hl, _⟩
        · exact ⟨h1, h2, by omega, h4⟩
        · rw [hl] at ha'; cases ha'
      · simp only [hact, Bool.false_eq_true, ite_false] at hc
        obtain ⟨_, ht, ht', ho⟩ := hc
        exact ⟨h1, by omega, by omega, .step h4 ho⟩

/-- **What a task call asks, sufficiently**: at a view `(vx, t, ongoing)`, a call within its timeout
before the deadline, after `n` idle periods, that keeps the business constraints from every hidden task
part the agent cannot rule out, after any outside changes, and is enabled. -/
theorem oblN_task (hD : sp.Design) {n : Nat} {l : sp.N} {i : (sp.tasks l).Inp} {vx : sp.VX}
    {t : Nat} (htime : t + n * sp.period + (sp.tasks l).dur i ≤ sp.d)
    (hB : ∀ x x₁ x₂, sp.viewX x = vx → sp.B x → sp.OutStar x x₁ → sp.B x₁ →
      (sp.tasks l).Dx i x₁ x₂ → sp.B x₂)
    (hen : ∀ x₁, ∃ x₂, (sp.tasks l).Dx i x₁ x₂) :
    sp.contract.OblN n ⟨.task l, i⟩ (vx, t, .ongoing) := by
  intro s s' ha ha' hv hc hw
  have hℓ' := (sp.active_iff s').1 ha'
  obtain ⟨hℓ, hts, ht', hout⟩ := sp.win_bound hw hℓ'
  have hvs : sp.viewX s.x = vx ∧ s.t = t := by
    simp only [contract, Prod.mk.injEq] at hv; exact ⟨hv.1, hv.2.1⟩
  have hBs := ((sp.C_iff hℓ).1 hc).1
  have hBs' := ((sp.C_iff hℓ').1 (sp.contract.win_C (sp.cert hD) hc hw)).1
  obtain ⟨x₂, hx₂⟩ := hen s'.x
  refine ⟨⟨⟨x₂, s'.t, s'.ℓ⟩, rfl, Nat.le_refl _, Nat.le_add_right _ _, hx₂⟩, ?_⟩
  intro s'' ⟨hl, _, ht'', hd⟩
  have ht''' : s''.t ≤ s'.t + (sp.tasks l).dur i := ht''
  refine Or.inl ⟨hB s.x s'.x s''.x hvs.1 hBs hout hBs' hd, ?_⟩
  rw [hvs.2] at ht'
  omega

/-- **A task call that can break the business constraints is rejected**: if, from some compliant task
part with the view `vx`, the call may lead to a task part that breaks them, its obligation is false,
whatever the allowance, so no proof is accepted. -/
theorem not_oblN_task {n : Nat} {l : sp.N} {i : (sp.tasks l).Inp} {vx : sp.VX} {t : Nat}
    (ht : t ≤ sp.d) (x x₂ : X) (hv : sp.viewX x = vx) (hB : sp.B x)
    (hd : (sp.tasks l).Dx i x x₂) (hB₂ : ¬ sp.B x₂) :
    ¬ sp.contract.OblN n ⟨.task l, i⟩ (vx, t, .ongoing) := by
  intro h
  have hadm := h ⟨x, t, .ongoing⟩ ⟨x, t, .ongoing⟩ ((sp.active_iff _).2 rfl)
    ((sp.active_iff _).2 rfl) (by simp [contract, hv]) ((sp.C_iff rfl).2 ⟨hB, ht⟩)
    (sp.contract.win_mono (Nat.zero_le n) rfl)
  have := hadm.2 ⟨x₂, t, .ongoing⟩ ⟨rfl, Nat.le_refl _, Nat.le_add_right _ _, hd⟩
  rcases this with ⟨hB', _⟩ | hne
  · exact hB₂ hB'
  · exact hne rfl

/-- **Settling before the goal holds is rejected**: if some compliant task part with the view `vx` does
not satisfy the goal, the settlement obligation is false, whatever the allowance. -/
theorem not_oblN_settle {n : Nat} {vx : sp.VX} {t : Nat} (ht : t ≤ sp.d) (x : X)
    (hv : sp.viewX x = vx) (hB : sp.B x) (hG : ¬ sp.Goal x) :
    ¬ sp.contract.OblN n ⟨.settle, ()⟩ (vx, t, .ongoing) := by
  intro h
  have hadm := h ⟨x, t, .ongoing⟩ ⟨x, t, .ongoing⟩ ((sp.active_iff _).2 rfl)
    ((sp.active_iff _).2 rfl) (by simp [contract, hv]) ((sp.C_iff rfl).2 ⟨hB, ht⟩)
    (sp.contract.win_mono (Nat.zero_le n) rfl)
  obtain ⟨⟨_, hd⟩, _⟩ := hadm
  exact hG ((sp.D_settle () _ _).1 hd).1

/-- **Settling once the goal holds**: at a view `(vx, t, ongoing)`, if every compliant task part with
that view satisfies the goal, and outside changes keep it, the settlement obligation holds for every
allowance. -/
theorem oblN_settle (hD : sp.Design) {n : Nat} {vx : sp.VX} {t : Nat}
    (hG : ∀ x x₁, sp.viewX x = vx → sp.B x → sp.OutStar x x₁ → sp.Goal x₁) :
    sp.contract.OblN n ⟨.settle, ()⟩ (vx, t, .ongoing) := by
  refine (sp.settle_obligation hD n (vx, t, .ongoing)).2 ?_
  intro s s' _ ha' hv hc hw
  have hℓ' := (sp.active_iff s').1 ha'
  obtain ⟨hℓ, _, _, hout⟩ := sp.win_bound hw hℓ'
  have hvs : sp.viewX s.x = vx := by simp only [contract, Prod.mk.injEq] at hv; exact hv.1
  exact hG s.x s'.x hvs ((sp.C_iff hℓ).1 hc).1 hout

end Spec

end Standard

end PC2
