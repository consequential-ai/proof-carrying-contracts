import PC2.Completion

/-!
# Appendix C: a design for the control step

The routine of §3.5.1 for any contract: it decides on the state it starts from, with decidable tests
`Ready`, `Act` and `Fix`; it starts the contract or leaves it inactive, idles, fixes, or terminates.
The conditions of App. C ("Establishing the certificate") give A3. Then the compute budget of App. C,
whose certificate is arithmetic.
-/

namespace PC2

variable {S : Type}

/-- **A control design** (§3.5.1): its tests, and the models of its branches. -/
structure Design (K : Contract S) where
  Ready : S → Bool
  Act : S → Bool
  Fix : S → Bool
  init : S → S → Prop
  noStart : S → S → Prop
  idle : S → S → Prop
  fix : S → S → Prop
  term : S → S → Prop

namespace Design

variable {K : Contract S} (D : Design K)

/-- The model of the routine of §3.5.1, deciding on the state it starts from. -/
def model (s s' : S) : Prop :=
  if K.stop s then (if D.Ready s then D.init s s' else D.noStart s s')
  else if D.Act s then (if D.Fix s then D.fix s s' else D.term s s')
  else D.idle s s'

/-- **The conditions of App. C.** Outside `Act`, a compliant active state is in `C_idle` (one idle period
keeps `C`); in `Act ∩ Fix` the fix keeps `C`; in `End = Act ∖ Fix` termination keeps `C` until the
contract closes; each branch is enabled where it is selected; from `Ready`, initialization lands in `C`;
elsewhere the contract stays inactive. -/
structure Sound : Prop where
  idle : ∀ s, K.Active s → K.C s → D.Act s = false → wp D.idle K.C s
  fix : ∀ s, K.Active s → K.C s → D.Act s = true → D.Fix s = true → wp D.fix K.C s
  term : ∀ s, K.Active s → K.C s → D.Act s = true → D.Fix s = false → wp D.term K.C s
  init : ∀ s, ¬ K.Active s → D.Ready s = true →
    (∃ s', D.init s s') ∧ ∀ s', D.init s s' → K.Active s' → K.C s'
  noStart : ∀ s, ¬ K.Active s → D.Ready s = false →
    (∃ s', D.noStart s s') ∧ ∀ s', D.noStart s s' → ¬ K.Active s'

/-- **The certificate from the design** (App. C): a contract whose control step follows a sound design
satisfies A3. -/
theorem cert (hctrl : ∀ s s', K.ctrl s s' ↔ D.model s s') (h : D.Sound) : K.Cert where
  controller s ha hc := by
    have hstop : K.stop s = false := ha
    have hm : ∀ s', K.ctrl s s' ↔ (if D.Act s then (if D.Fix s then D.fix s s' else D.term s s')
        else D.idle s s') := fun s' => by rw [hctrl, model, hstop]; simp
    by_cases hact : D.Act s = true
    · by_cases hfix : D.Fix s = true
      · obtain ⟨⟨s', hs'⟩, hall⟩ := h.fix s ha hc hact hfix
        exact ⟨⟨s', (hm s').2 (by simp [hact, hfix, hs'])⟩,
          fun s' hs => hall s' (by have := (hm s').1 hs; simpa [hact, hfix] using this)⟩
      · have hfix' : D.Fix s = false := by simpa using hfix
        obtain ⟨⟨s', hs'⟩, hall⟩ := h.term s ha hc hact hfix'
        exact ⟨⟨s', (hm s').2 (by simp [hact, hfix', hs'])⟩,
          fun s' hs => hall s' (by have := (hm s').1 hs; simpa [hact, hfix'] using this)⟩
    · have hact' : D.Act s = false := by simpa using hact
      obtain ⟨⟨s', hs'⟩, hall⟩ := h.idle s ha hc hact'
      exact ⟨⟨s', (hm s').2 (by simp [hact', hs'])⟩,
        fun s' hs => hall s' (by have := (hm s').1 hs; simpa [hact'] using this)⟩
  initializer s s' hin ha' hs := by
    have hstop : K.stop s = true := by
      cases h' : K.stop s
      · exact absurd h' hin
      · rfl
    rw [hctrl, model, hstop] at hs
    by_cases hr : D.Ready s = true
    · simp only [hr, ite_true] at hs
      exact (h.init s hin hr).2 s' hs ha'
    · have hr' : D.Ready s = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, ite_false, ite_true] at hs
      exact absurd ha' ((h.noStart s hin hr').2 s' hs)
  enabled s hin := by
    have hstop : K.stop s = true := by
      cases h' : K.stop s
      · exact absurd h' hin
      · rfl
    by_cases hr : D.Ready s = true
    · obtain ⟨s', hs'⟩ := (h.init s hin hr).1
      exact ⟨s', (hctrl s s').2 (by rw [model, hstop]; simp [hr, hs'])⟩
    · have hr' : D.Ready s = false := by simpa using hr
      obtain ⟨s', hs'⟩ := (h.noStart s hin hr').1
      exact ⟨s', (hctrl s s').2 (by rw [model, hstop]; simp [hr', hs'])⟩

end Design

/-! ## The compute budget (App. C) -/

namespace ComputeBudget

/-- The state: the bill `b`, a bound `r` on the charging rate of the running jobs, the remaining
shutdown allowance `h`, the time `t`, and the label. -/
structure St where
  b : Nat
  r : Nat
  h : Nat
  t : Nat
  ℓ : Label

variable (B d p : Nat)

/-- The clause: the bill, with the maximum charge while the jobs stop, stays within the budget, at every
instant, closing included; while the contract is ongoing, the time is within the deadline. The reserve
`r * h` is for the budget: the jobs are charged until they have stopped. -/
def C (s : St) : Prop := s.b + s.r * s.h ≤ B ∧ (s.ℓ = .ongoing → s.t ≤ d)

/-- The waiting tests, which certify `C_idle`: one more period, and a shutdown after it, stay within the
budget and before the deadline. -/
def waitOK (s : St) : Bool := decide (s.b + s.r * (p + s.h) ≤ B) && decide (s.t + p + s.h ≤ d)

/-- Outside changes during `u ≤ p` units of waiting: the bill rises at most at rate `r`, jobs may stop,
time advances; the label is kept. -/
def idle (s s' : St) : Prop :=
  ∃ u, u ≤ p ∧ s'.b ≤ s.b + s.r * u ∧ s'.r ≤ s.r ∧ s'.h ≤ s.h ∧ s'.t = s.t + u ∧ s'.ℓ = s.ℓ

/-- Stopping the jobs, after `u ≤ h` units: the bill rises at most at rate `r`, the allowance counts
down. -/
def shut (s s' : St) : Prop :=
  ∃ u, u ≤ s.h ∧ s'.b ≤ s.b + s.r * u ∧ s'.r ≤ s.r ∧ s'.h ≤ s.h - u ∧ s'.t = s.t + u

/-- The control design, closing first: start only where the waiting tests hold; idle where they hold;
where only the budget test fails, fix by stopping the jobs and staying ongoing; where the time test
fails, close the contract at once, and stop the jobs with the contract closed. -/
def design : Design (⟨C B d, St, id, Empty, fun e => e.elim, fun _ _ => False,
    fun s => s.ℓ != .ongoing⟩ : Contract St) where
  Ready s := waitOK B d p s && (s.ℓ == .pending)
  Act s := !waitOK B d p s
  Fix s := decide (s.t + p + s.h ≤ d)
  init s s' := s' = s ∨ s' = { s with ℓ := .ongoing }
  noStart s s' := s' = s
  idle := idle p
  fix s s' := shut s s' ∧ s'.ℓ = .ongoing
  term s s' := s' = s ∨ (s'.ℓ = .terminated ∧ shut s s')

/-- Stopping the jobs keeps the bill, with the remaining reserve, within its starting bound, and takes
at most the allowance. -/
theorem shut_C {s s' : St} (hs : shut s s') :
    s'.b + s'.r * s'.h ≤ s.b + s.r * s.h ∧ s'.t ≤ s.t + s.h := by
  obtain ⟨u, hu, hb', hr', hh', ht'⟩ := hs
  have h1 : s'.r * s'.h ≤ s.r * (s.h - u) := Nat.mul_le_mul hr' hh'
  have h2 : s.r * u + s.r * (s.h - u) = s.r * s.h := by
    rw [← Nat.mul_add, Nat.add_sub_cancel' hu]
  constructor <;> omega

/-- **The compute budget's design is sound**, so the contract satisfies A3: the certificate is
arithmetic, with no reserve of time. -/
theorem sound : (design B d p).Sound where
  idle s _ hc hact := by
    have hw : waitOK B d p s = true := by simpa [design] using hact
    simp only [waitOK, Bool.and_eq_true, decide_eq_true_eq] at hw
    refine ⟨⟨s, 0, Nat.zero_le _, by simp, Nat.le_refl _, Nat.le_refl _, by simp, rfl⟩, ?_⟩
    intro s' ⟨u, hu, hb', hr', hh', ht', hl⟩
    have h1 : s'.r * s'.h ≤ s.r * s.h := Nat.mul_le_mul hr' hh'
    have h2 : s.r * u ≤ s.r * p := Nat.mul_le_mul_left _ hu
    have h3 : s.r * (p + s.h) = s.r * p + s.r * s.h := Nat.mul_add _ _ _
    refine ⟨by omega, fun _ => by omega⟩
  fix s ha hc _ hfix := by
    have hd : s.t + p + s.h ≤ d := by simpa [design] using hfix
    refine ⟨⟨s, ⟨0, Nat.zero_le _, by simp, Nat.le_refl _, by simp, by simp⟩, ?_⟩, ?_⟩
    · simpa [Contract.Active] using ha
    · intro s' ⟨hs, _⟩
      obtain ⟨hb', ht'⟩ := shut_C hs
      exact ⟨by have := hc.1; omega, fun _ => by omega⟩
  term s _ hc _ _ := by
    refine ⟨⟨s, Or.inl rfl⟩, ?_⟩
    intro s' hs
    rcases hs with rfl | ⟨hl, hs⟩
    · exact hc
    · obtain ⟨hb', _⟩ := shut_C hs
      exact ⟨by have := hc.1; omega, fun h => by rw [hl] at h; cases h⟩
  init s _ hr := by
    have hw : waitOK B d p s = true ∧ s.ℓ = .pending := by simpa [design] using hr
    have hw' := hw.1
    simp only [waitOK, Bool.and_eq_true, decide_eq_true_eq] at hw'
    refine ⟨⟨s, Or.inl rfl⟩, fun s' hs ha' => ?_⟩
    rcases hs with rfl | rfl
    · simp [Contract.Active, hw.2] at ha'
    · have h3 : s.r * (p + s.h) = s.r * p + s.r * s.h := Nat.mul_add _ _ _
      exact ⟨by simp; omega, fun _ => by simp; omega⟩
  noStart s hin _ := ⟨⟨s, rfl⟩, fun s' hs => by subst hs; exact hin⟩

end ComputeBudget

end PC2
