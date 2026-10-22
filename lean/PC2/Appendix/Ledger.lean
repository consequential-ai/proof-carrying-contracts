import PC2.World

/-!
# Appendix E: two worked examples of correspondence

The payment ledger (Proposition E.1, adequacy by summing, the bound after closing) and booking
confirmations (Proposition E.2, and the step to a goal in the world).
-/

namespace PC2

/-- The sum of a function over a list of identifiers. -/
def sumOver {Id : Type} (ids : List Id) (f : Id → Nat) : Nat := (ids.map f).sum

theorem sumOver_le {Id : Type} (ids : List Id) {f g : Id → Nat} (h : ∀ j, f j ≤ g j) :
    sumOver ids f ≤ sumOver ids g := by
  induction ids with
  | nil => simp [sumOver]
  | cons j js ih =>
    simp only [sumOver, List.map_cons, List.sum_cons] at ih ⊢
    have := h j; omega

section Ledger

variable {Id Wl Sl : Type} (r : Sl → Id → Nat) (u a : Wl → Id → Nat)

/-- The ledger's correspondence (Eq. budget-correspondence): every charge stays within its issued limit,
and every issued limit within its reservation. -/
def ledgerρ (w : Wl) (s : Sl) : Prop := ∀ j, a w j ≤ u w j ∧ u w j ≤ r s j

/-- **The reservation discipline**, from `(w, s)` to `(w', s')`: reservations are never removed or
lowered; an issued limit never changes, and a new one is issued only once its reservation covers it. -/
def Reservation (w : Wl) (s : Sl) (w' : Wl) (s' : Sl) : Prop :=
  (∀ j, r s j ≤ r s' j) ∧ ∀ j, u w' j = u w j ∨ (u w j = 0 ∧ u w' j ≤ r s' j)

/-- **The service condition**: the charges under an instruction stay within its limit. -/
def ServiceCond (w : Wl) : Prop := ∀ j, a w j ≤ u w j

/-- **Proposition E.1 (Preserving budget correspondence).** The reservation discipline and the service
condition preserve the correspondence. -/
theorem budget_correspondence {w w' : Wl} {s s' : Sl} (hρ : ledgerρ r u a w s)
    (hres : Reservation r u w s w' s') (hsvc : ServiceCond u a w') : ledgerρ r u a w' s' := by
  intro j
  refine ⟨hsvc j, ?_⟩
  rcases hres.2 j with h | ⟨_, h⟩
  · rw [h]; exact Nat.le_trans (hρ j).2 (hres.1 j)
  · exact h

/-- In particular, they give the first line of A5: if every effect of the deployment satisfies them,
from where the operation starts, every operation preserves the correspondence. -/
theorem ledger_fidelity {S W : Type} {K : Contract S} {E : Effects K W} (r : S → Id → Nat)
    (u a : W → Id → Nat)
    (hcall : ∀ c w s w' s', E.call c w s w' s' → Reservation r u w s w' s' ∧ ServiceCond u a w')
    (hctrl : ∀ w s w' s', E.ctrl w s w' s' → Reservation r u w s w' s' ∧ ServiceCond u a w') :
    (∀ c w s w' s', ledgerρ r u a w s → E.call c w s w' s' → ledgerρ r u a w' s') ∧
      (∀ w s w' s', ledgerρ r u a w s → E.ctrl w s w' s' → ledgerρ r u a w' s') :=
  ⟨fun c w s w' s' hρ he => budget_correspondence r u a hρ (hcall c w s w' s' he).1
      (hcall c w s w' s' he).2,
   fun w s w' s' hρ he => budget_correspondence r u a hρ (hctrl w s w' s' he).1
      (hctrl w s w' s' he).2⟩

/-- **Adequacy for the budget** (App. E): summing the correspondence, the charges are bounded by the
reservations, so a clause bounding the reservations bounds the charges. -/
theorem budget_adequacy (ids : List Id) (B : Nat) {w : Wl} {s : Sl} (hρ : ledgerρ r u a w s)
    (hC : sumOver ids (r s) ≤ B) : sumOver ids (a w) ≤ B :=
  Nat.le_trans (sumOver_le ids fun j => Nat.le_trans (hρ j).1 (hρ j).2) hC

/-- **The bound after closing** (Eq. post-closing budget): if no limit is issued or changed after
closing and the service condition keeps holding, the reservations at closing still bound the
charges. -/
theorem budget_after_closing (ids : List Id) {wc w : Wl} {sc : Sl} (hρ : ledgerρ r u a wc sc)
    (hu : ∀ j, u w j = u wc j) (hsvc : ServiceCond u a w) :
    sumOver ids (a w) ≤ sumOver ids (r sc) :=
  sumOver_le ids fun j => Nat.le_trans (hsvc j) (by rw [hu j]; exact (hρ j).2)

end Ledger

section Booking

variable {Bk Wb Sb : Type} (R : Sb → Bk → Nat → Prop) (Issued : Wb → Bk → Nat → Prop)
  (Held : Wb → Bk → Prop) (tW : Wb → Nat)

/-- The booking correspondence (Eq. booking-correspondence): each recorded confirmation `(b, d)` was
issued by the agreed service, and the reservation is held before its expiry `d`. -/
def bookingρ (w : Wb) (s : Sb) : Prop :=
  ∀ b d, R s b d → Issued w b d ∧ (tW w < d → Held w b)

/-- **Proposition E.2 (Preserving booking correspondence).** The recording condition (entries are
added only from confirmations issued by the service), the reservation condition (an issued confirmation
is held until its expiry) and the retention of the service's history preserve the correspondence. -/
theorem booking_correspondence {w w' : Wb} {s s' : Sb} (hρ : bookingρ R Issued Held tW w s)
    (hrec : ∀ b d, R s' b d → R s b d ∨ Issued w' b d)
    (hres : ∀ b d, Issued w' b d → tW w' < d → Held w' b)
    (hret : ∀ b d, Issued w b d → Issued w' b d) : bookingρ R Issued Held tW w' s' := by
  intro b d hR
  have hI : Issued w' b d := by
    rcases hrec b d hR with h | h
    · exact hret b d (hρ b d h).1
    · exact h
  exact ⟨hI, hres b d hI⟩

/-- **From a recorded confirmation to a held reservation** (App. E): with a conservative clock in the
correspondence (`t_W(w) ≤ t`), a recorded confirmation that has not expired by the state's clock is
held in the world. -/
theorem booking_goal {w : Wb} {s : Sb} {b : Bk} {d t : Nat} (hρ : bookingρ R Issued Held tW w s)
    (hR : R s b d) (hclock : tW w ≤ t) (hexp : t < d) : Held w b :=
  (hρ b d hR).2 (Nat.lt_of_le_of_lt hclock hexp)

end Booking

end PC2
