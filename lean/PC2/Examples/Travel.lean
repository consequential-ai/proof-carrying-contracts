import PC2.Guarantees
import PC2.Appendix.WP

/-!
# The travel contract (Table 1) and the session of Fig. 2

The travel contract as a standard contract. The task part records the commitments, the recipients of the
passport, the bookings, the expert's ratings, the mail read, the visa and the escrow; the passport itself
is never part of what the agent sees. Every episode of Fig. 2 is a checked statement: the calls that are
rejected have a false obligation, so no proof is accepted, whatever the allowance; the calls that run
have a proof, the one the agent submits.
-/

namespace PC2

namespace Travel

open Standard

/-- The visa; the consulate's decision is final. -/
inductive Visa where
  | pending
  | granted
  | refused
  deriving DecidableEq, Repr

/-- The escrow, held by the Airlock. -/
inductive Escrow where
  | locked
  | paid
  | refunded
  deriving DecidableEq, Repr

/-- The task part of the travel contract. -/
structure X where
  /-- Commitments, fees included. -/
  spent : Nat
  /-- To whom the passport was sent. -/
  discl : List String
  /-- Bookings: hotel, night, amount. -/
  booked : List (String × Nat × Nat)
  /-- The expert's ratings, as recorded: hotel, rating. -/
  ratings : List (String × Nat)
  /-- The mail read: sender, body. -/
  inbox : List (String × String)
  visa : Visa
  escrow : Escrow
  deriving DecidableEq, Repr

/-- The first recorded rating of a hotel in a list of ratings, `0` if none. -/
def lookup (h : String) : List (String × Nat) → Nat
  | [] => 0
  | (h', r) :: rs => if h' = h then r else lookup h rs

/-- The recorded rating of a hotel, `0` if the expert was not asked. -/
def X.rating (x : X) (h : String) : Nat := lookup h x.ratings

/-- The designated consulate. -/
def consulate : String := "consulate"

/-- **The constraints at every instant** (Table 1): at most 2000 in commitments, fees included; the
passport only to the designated consulate; every booked hotel with a recorded rating of at least 7. -/
def B (x : X) : Prop :=
  x.spent ≤ 2000 ∧ (∀ r ∈ x.discl, r = consulate) ∧ ∀ e ∈ x.booked, 7 ≤ x.rating e.1

instance : DecidablePred B := fun x => by unfold B; exact inferInstance

/-- **The goal** (Table 1): confirmed bookings for nights 1–3, and a granted visa. -/
def Goal (x : X) : Prop := (∀ n ∈ [1, 2, 3], ∃ e ∈ x.booked, e.2.1 = n) ∧ x.visa = .granted

instance : DecidablePred Goal := fun x => by unfold Goal; exact inferInstance

/-- **Outside changes**: mail may arrive, and the consulate may decide on the visa; nothing else
changes. -/
def out (x x' : X) : Prop :=
  x'.spent = x.spent ∧ x'.discl = x.discl ∧ x'.booked = x.booked ∧ x'.ratings = x.ratings ∧
    x'.escrow = x.escrow ∧ (∃ new, x'.inbox = x.inbox ++ new) ∧
    (x.visa = .pending ∨ x'.visa = x.visa)

/-- The tools of the task. -/
inductive N where
  | rate
  | book
  | downloadMail
  | sendPassport

/-- What each tool does to the task part, before the outside changes during the call. -/
def eff : (l : N) → (match l with
    | .rate => String | .book => String × Nat × Nat | .downloadMail => Unit
    | .sendPassport => String) → X → X → Prop
  | .rate, h, x, y => y = x ∨ (x.rating h = 0 ∧ h ∉ x.ratings.map (·.1) ∧
      ∃ r, r ≤ 10 ∧ y = { x with ratings := (h, r) :: x.ratings })
  | .book, (h, n, m), x, y => y = x ∨ y = { x with booked := (h, n, m) :: x.booked, spent := x.spent + m }
  | .downloadMail, _, x, y => ∃ new, y = { x with inbox := x.inbox ++ new }
  | .sendPassport, r, x, y => y = x ∨ y = { x with discl := r :: x.discl }

/-- The task tools: `rate` (the expert, its answer recorded once), `book` (the amount caps the charge,
fees included), `download_mail`, `sendPassport`; each lasts at most a minute. -/
def tasks : N → Standard.Task X
  | .rate => ⟨String, fun h x x' => ∃ y, eff .rate h x y ∧ out y x', fun _ => 60⟩
  | .book => ⟨String × Nat × Nat, fun i x x' => ∃ y, eff .book i x y ∧ out y x', fun _ => 60⟩
  | .downloadMail => ⟨Unit, fun i x x' => ∃ y, eff .downloadMail i x y ∧ out y x', fun _ => 60⟩
  | .sendPassport => ⟨String, fun r x x' => ∃ y, eff .sendPassport r x y ∧ out y x', fun _ => 60⟩

/-- The deadline: 30 days after signing, in seconds. -/
def deadline : Nat := 30 * 24 * 3600

/-- **The travel contract** (Table 1), as a standard contract. The agent sees the whole task part (the
passport's contents are not part of it); control checks every minute, and terminates at the deadline or
upon visa refusal, refunding the escrow. -/
def spec : Spec X where
  VX := X
  viewX := id
  B := B
  Goal := Goal
  d := deadline
  N := N
  tasks := tasks
  pay x x' := x' = { x with escrow := .paid }
  Ready x t := x.spent == 0 && x.discl.isEmpty && x.booked.isEmpty && x.escrow == .locked &&
    decide (t + 60 ≤ deadline)
  initX x x' := x' = x
  initDur := 60
  voidX x x' := x' = x
  out := out
  period := 60
  endX x := x.visa == .refused
  refund x x' := x' = { x with escrow := .refunded }

instance : DecidablePred spec.B := fun x => inferInstanceAs (Decidable (B x))
instance : DecidablePred spec.Goal := fun x => inferInstanceAs (Decidable (Goal x))

theorem out_refl (x : X) : out x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨[], by simp⟩, Or.inr rfl⟩

theorem out_B {x x' : X} (hB : B x) (h : out x x') : B x' := by
  obtain ⟨hs, hd, hb, hr, _, _, _⟩ := h
  have hrat : ∀ h', x'.rating h' = x.rating h' := fun h' => by simp [X.rating, hr]
  obtain ⟨h1, h2, h3⟩ := hB
  exact ⟨hs ▸ h1, hd ▸ h2, fun e he => by rw [hrat]; exact h3 e (hb ▸ he)⟩

/-- **The design obligations hold**, so the travel contract satisfies A3 (`Spec.cert`). -/
theorem design : spec.Design where
  init_ok x t x' t' hr hi ht := by
    simp only [spec, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, decide_eq_true_eq] at hr
    obtain ⟨⟨⟨⟨hs, hd⟩, hb⟩, _⟩, htd⟩ := hr
    have hi' : x' = x := hi
    have hdur : spec.initDur = 60 := rfl
    rw [hi']
    exact ⟨⟨by omega, by simp [hd], by simp [hb]⟩, by show t' ≤ deadline; omega⟩
  out_refl := out_refl
  out_B _ _ hB h := out_B hB h

/-- The travel contract's certificate: A3. -/
theorem cert : spec.contract.Cert := spec.cert design

/-! ## What each call asks -/

theorem outStar_B {x x' : X} (hB : B x) (h : spec.OutStar x x') : B x' := by
  induction h with
  | refl => exact hB
  | step _ ho ih => exact out_B ih ho

theorem outStar_fields {x x' : X} (h : spec.OutStar x x') :
    x'.spent = x.spent ∧ x'.discl = x.discl ∧ x'.booked = x.booked ∧ x'.ratings = x.ratings := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl, rfl⟩
  | step _ ho ih =>
    obtain ⟨hs, hd, hb, hr, _⟩ := ho
    exact ⟨hs.trans ih.1, hd.trans ih.2.1, hb.trans ih.2.2.1, hr.trans ih.2.2.2⟩

theorem outStar_goal {x x' : X} (hG : Goal x) (h : spec.OutStar x x') : Goal x' := by
  induction h with
  | refl => exact hG
  | step _ ho ih =>
    obtain ⟨_, _, hb, _, _, _, hv⟩ := ho
    refine ⟨fun n hn => by rw [hb]; exact ih.1 n hn, ?_⟩
    rcases hv with h | h
    · rw [ih.2] at h; cases h
    · rw [h]; exact ih.2

theorem rating_cons {x : X} {h h' : String} {r : Nat} (hne : h' ≠ h) :
    ({ x with ratings := (h, r) :: x.ratings } : X).rating h' = x.rating h' := by
  simp [X.rating, lookup, Ne.symm hne]

/-- **The expert's answer is recorded** (memoization): asking again leaves a recorded rating
unchanged. -/
theorem rate_memo {x x' : X} {h : String} (hrated : h ∈ x.ratings.map (·.1))
    (hd : (tasks .rate).Dx h x x') : x'.rating h = x.rating h := by
  obtain ⟨y, hy, ho⟩ := hd
  have hr : x'.ratings = y.ratings := ho.2.2.2.1
  rcases hy with rfl | ⟨_, hnot, _⟩
  · simp [X.rating, hr]
  · exact absurd hrated hnot

theorem rate_keeps_B {x x' : X} {h : String} (hB : B x) (hd : (tasks .rate).Dx h x x') : B x' := by
  obtain ⟨y, hy, ho⟩ := hd
  refine out_B ?_ ho
  rcases hy with rfl | ⟨h0, _, r, _, rfl⟩
  · exact hB
  · obtain ⟨h1, h2, h3⟩ := hB
    refine ⟨h1, h2, fun e he => ?_⟩
    have hne : e.1 ≠ h := fun heq => by have := h3 e he; rw [heq, h0] at this; omega
    rw [rating_cons hne]; exact h3 e he

theorem book_keeps_B {x x' : X} {h : String} {n m : Nat} (hB : B x) (hm : x.spent + m ≤ 2000)
    (hr : 7 ≤ x.rating h) (hd : (tasks .book).Dx (h, n, m) x x') : B x' := by
  obtain ⟨y, hy, ho⟩ := hd
  refine out_B ?_ ho
  rcases hy with rfl | rfl
  · exact hB
  · obtain ⟨_, h2, h3⟩ := hB
    refine ⟨hm, h2, fun e he => ?_⟩
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · exact hr
    · exact h3 e he

theorem download_keeps_B {x x' : X} (hB : B x) (hd : (tasks .downloadMail).Dx () x x') : B x' := by
  obtain ⟨y, ⟨new, rfl⟩, ho⟩ := hd
  have hBy : B { x with inbox := x.inbox ++ new } :=
    ⟨hB.1, hB.2.1, fun e he => by simpa [X.rating] using hB.2.2 e he⟩
  exact out_B hBy ho

theorem send_keeps_B {x x' : X} {r : String} (hB : B x) (hr : r = consulate)
    (hd : (tasks .sendPassport).Dx r x x') : B x' := by
  obtain ⟨y, hy, ho⟩ := hd
  refine out_B ?_ ho
  rcases hy with rfl | rfl
  · exact hB
  · refine ⟨hB.1, fun r' hr' => ?_, fun e he => by simpa [X.rating] using hB.2.2 e he⟩
    simp only [List.mem_cons] at hr'
    rcases hr' with rfl | hr'
    · exact hr
    · exact hB.2.1 r' hr'

theorem tasks_en (l : N) (i : (tasks l).Inp) (x : X) : ∃ x', (tasks l).Dx i x x' := by
  cases l with
  | rate => exact ⟨x, x, Or.inl rfl, out_refl x⟩
  | book => exact ⟨x, x, Or.inl rfl, out_refl x⟩
  | downloadMail => exact ⟨x, x, ⟨[], by simp⟩, out_refl x⟩
  | sendPassport => exact ⟨x, x, Or.inl rfl, out_refl x⟩

/-- Asking the expert is admissible at any compliant view, before the deadline. -/
theorem rate_ok {n t : Nat} {x : X} (h : String) (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .rate, h⟩ (x, t, .ongoing) :=
  spec.oblN_task design ht (fun _ _ _ _ _ _ hB₁ hd => rate_keeps_B hB₁ hd) (tasks_en .rate h)

/-- Booking a hotel rated at least 7, within the budget, is admissible. -/
theorem book_ok {n t : Nat} {x : X} {h : String} {night m : Nat} (hm : x.spent + m ≤ 2000)
    (hr : 7 ≤ x.rating h) (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .book, (h, night, m)⟩ (x, t, .ongoing) := by
  refine spec.oblN_task design ht (fun x₀ x₁ _ hv _ hout hB₁ hd => ?_) (tasks_en .book _)
  have hx₀ : x₀ = x := hv
  subst hx₀
  obtain ⟨hs, _, _, hrt⟩ := outStar_fields hout
  exact book_keeps_B hB₁ (by rw [hs]; exact hm) (by simp only [X.rating, hrt] at hr ⊢; exact hr) hd

/-- Downloading mail is admissible at any compliant view, before the deadline. -/
theorem download_ok {n t : Nat} {x : X} (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .downloadMail, ()⟩ (x, t, .ongoing) :=
  spec.oblN_task design ht (fun _ _ _ _ _ _ hB₁ hd => download_keeps_B hB₁ hd)
    (tasks_en .downloadMail ())

/-- Sending the passport to the consulate is admissible. -/
theorem send_ok {n t : Nat} {x : X} (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .sendPassport, consulate⟩ (x, t, .ongoing) :=
  spec.oblN_task design ht (fun _ _ _ _ _ _ hB₁ hd => send_keeps_B hB₁ rfl hd)
    (tasks_en .sendPassport consulate)

/-- Settling once the goal holds is admissible: the goal survives outside changes. -/
theorem settle_ok {n t : Nat} {x : X} (hG : Goal x) :
    spec.contract.OblN n ⟨.settle, ()⟩ (x, t, .ongoing) :=
  spec.oblN_settle design fun x₀ _ hv _ hout => by
    have hx₀ : x₀ = x := hv
    subst hx₀
    exact outStar_goal hG hout

/-! ## The session of Fig. 2 -/

/-- The task part at the start: nothing spent, sent or booked, no rating, no mail, visa pending, escrow
locked. -/
def x₀ : X := ⟨0, [], [], [], [], .pending, .locked⟩

/-- After the expert rated Belvedere 5 and Aurora 8. -/
def x₁ : X := { x₀ with ratings := [("Aurora", 8), ("Belvedere", 5)] }

/-- After booking Aurora for night 1 at 900. -/
def x₂ : X := { x₁ with booked := [("Aurora", 1, 900)], spent := 900 }

/-- Once the three nights are booked, the passport sent to the consulate and the visa granted. -/
def x₃ : X :=
  { x₂ with
    booked := [("Aurora", 3, 500), ("Aurora", 2, 500), ("Aurora", 1, 900)]
    spent := 1900
    discl := [consulate]
    visa := .granted }

/-- **Episode 1.** Booking the partner hotel, which the expert has not rated, has no proof, whatever the
allowance. -/
theorem ep1_book_rejected (n t : Nat) (ht : t ≤ deadline) :
    ¬ spec.contract.OblN n ⟨.task .book, ("Belvedere", 1, 260)⟩ (x₀, t, .ongoing) :=
  spec.not_oblN_task ht x₀ { x₀ with booked := [("Belvedere", 1, 260)], spent := 260 } rfl
    (by decide) ⟨_, Or.inr rfl, out_refl _⟩ (by decide)

/-- **Episode 1.** Asking the expert is admissible; asking again returns the recorded rating. -/
theorem ep1_rate (n t : Nat) (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .rate, "Belvedere"⟩ (x₀, t, .ongoing) := rate_ok _ ht

theorem ep1_rate_again {x' : X} (hd : (tasks .rate).Dx "Belvedere" x₁ x') :
    x'.rating "Belvedere" = 5 :=
  (rate_memo (by decide) hd).trans (by decide)

/-- **Episode 2.** Booking Aurora, rated 8, for 900: the agent's proof. A policy that capped each night
at 600 would reject it, although it keeps the budget (`policy_engine_example`). -/
theorem ep2_book (n t : Nat) (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .book, ("Aurora", 1, 900)⟩ (x₁, t, .ongoing) :=
  book_ok (by decide) (by decide) ht

/-- **Episode 3.** Downloading the mail is admissible, whatever arrives; sending the passport to the
address of the injected message has no proof. -/
theorem ep3_download (n t : Nat) (ht : t + n * 60 + 60 ≤ deadline) :
    spec.contract.OblN n ⟨.task .downloadMail, ()⟩ (x₂, t, .ongoing) := download_ok ht

theorem ep3_injection_rejected (n t : Nat) (ht : t ≤ deadline) :
    ¬ spec.contract.OblN n ⟨.task .sendPassport, "x@visa.io"⟩ (x₂, t, .ongoing) :=
  spec.not_oblN_task ht x₂ { x₂ with discl := ["x@visa.io"] } rfl (by decide)
    ⟨_, Or.inr rfl, out_refl _⟩ (by decide)

/-- **Episode 4.** Settling while the visa is pending has no proof; once the goal holds, settling is
admissible, and the escrow is released without further approval. -/
theorem ep4_premature (n t : Nat) (ht : t ≤ deadline) :
    ¬ spec.contract.OblN n ⟨.settle, ()⟩ (x₂, t, .ongoing) :=
  spec.not_oblN_settle ht x₂ rfl (by decide) (by decide)

theorem ep4_settle (n t : Nat) : spec.contract.OblN n ⟨.settle, ()⟩ (x₃, t, .ongoing) :=
  settle_ok (by decide)

end Travel

end PC2
