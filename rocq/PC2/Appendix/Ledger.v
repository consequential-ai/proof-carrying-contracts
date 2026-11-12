(** * Appendix E: two worked examples of correspondence

The payment ledger (Proposition E.1, adequacy by summing, the bound after
closing) and booking confirmations (Proposition E.2, and the step to a goal in
the world). *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From PC2 Require Import Basic Airlock Execution.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Section Ledger.

Variables (Id Wl Sl : Type) (r : Sl -> Id -> nat) (u a : Wl -> Id -> nat).

(** The ledger's correspondence (Eq. budget-correspondence): every charge stays
within its issued limit, and every issued limit within its reservation. *)
Definition ledgerρ (w : Wl) (s : Sl) : Prop :=
  forall j, a w j <= u w j <= r s j.

(** **The reservation discipline**, from [(w, s)] to [(w', s')]: reservations
are never removed or lowered; an issued limit never changes, and a new one is
issued only once its reservation covers it. *)
Definition Reservation (w : Wl) (s : Sl) (w' : Wl) (s' : Sl) : Prop :=
  (forall j, r s j <= r s' j) /\
  forall j, u w' j = u w j \/ (u w j = 0 /\ u w' j <= r s' j).

(** **The service condition**: the charges under an instruction stay within its
limit. *)
Definition ServiceCond (w : Wl) : Prop := forall j, a w j <= u w j.

(** **Proposition E.1 (Preserving budget correspondence).** The reservation
discipline and the service condition preserve the correspondence. *)
Lemma budget_correspondence {w w' : Wl} {s s' : Sl} :
  ledgerρ w s -> Reservation w s w' s' -> ServiceCond w' -> ledgerρ w' s'.
Proof.
move=> hρ [hr hu] hsvc j; rewrite hsvc /=.
by case: (hu j) => [->|[_ //]]; case/andP: (hρ j) => _ /leq_trans; apply.
Qed.

(** **Adequacy for the budget** (App. E): summing the correspondence, the
charges are bounded by the reservations, so a clause bounding the reservations
bounds the charges. *)
Lemma budget_adequacy (ids : seq Id) (B : nat) {w : Wl} {s : Sl} :
  ledgerρ w s -> \sum_(j <- ids) r s j <= B -> \sum_(j <- ids) a w j <= B.
Proof.
move=> hρ; apply: leq_trans; apply: leq_sum => j _.
by case/andP: (hρ j); exact: leq_trans.
Qed.

(** **The bound after closing** (Eq. post-closing budget): if no limit is issued
or changed after closing and the service condition keeps holding, the
reservations at closing still bound the charges. *)
Lemma budget_after_closing (ids : seq Id) {wc w : Wl} {sc : Sl} :
  ledgerρ wc sc -> (forall j, u w j = u wc j) -> ServiceCond w ->
  \sum_(j <- ids) a w j <= \sum_(j <- ids) r sc j.
Proof.
move=> hρ hu hsvc; apply: leq_sum => j _.
by apply: leq_trans (hsvc j) _; rewrite hu; case/andP: (hρ j).
Qed.

End Ledger.

Arguments ledgerρ {Id Wl Sl} r u a w s.
Arguments Reservation {Id Wl Sl} r u w s w' s'.
Arguments ServiceCond {Id Wl} u a w.
Arguments budget_correspondence {Id Wl Sl} r u a {w w' s s'} _ _ _.
Arguments budget_adequacy {Id Wl Sl} r u a ids B {w s} _ _.
Arguments budget_after_closing {Id Wl Sl} r u a ids {wc w sc} _ _ _.

(** In particular, they give the first line of A5: if every effect of the
deployment satisfies them, from where the operation starts, every operation
preserves the correspondence. *)
Lemma ledger_fidelity {Id S W : Type} {K : Contract S} {E : Effects K W}
    (r : S -> Id -> nat) (u a : W -> Id -> nat)
    (hcall : forall c w s w' s', Effects.ecall E c w s w' s' ->
      Reservation r u w s w' s' /\ ServiceCond u a w')
    (hctrl : forall w s w' s', Effects.ectrl E w s w' s' ->
      Reservation r u w s w' s' /\ ServiceCond u a w') :
  (forall c w s w' s', ledgerρ r u a w s -> Effects.ecall E c w s w' s' ->
    ledgerρ r u a w' s') /\
  (forall w s w' s', ledgerρ r u a w s -> Effects.ectrl E w s w' s' ->
    ledgerρ r u a w' s').
Proof.
split=> [c w s w' s' hρ /hcall[hr hs]|w s w' s' hρ /hctrl[hr hs]];
  exact: budget_correspondence hρ hr hs.
Qed.

Section Booking.

Variables (Bk Wb Sb : Type) (R : Sb -> Bk -> nat -> Prop)
  (Issued : Wb -> Bk -> nat -> Prop)
  (Held : Wb -> Bk -> Prop) (tW : Wb -> nat).

(** The booking correspondence (Eq. booking-correspondence): each recorded
confirmation [(b, d)] was issued by the agreed service, and the reservation is
held before its expiry [d]. *)
Definition bookingρ (w : Wb) (s : Sb) : Prop :=
  forall b d, R s b d -> Issued w b d /\ (tW w < d -> Held w b).

(** **Proposition E.2 (Preserving booking correspondence).** The recording
condition (entries are added only from confirmations issued by the service), the
reservation condition (an issued confirmation is held until its expiry) and the
retention of the service's history preserve the correspondence. *)
Lemma booking_correspondence {w w' : Wb} {s s' : Sb} :
  bookingρ w s -> (forall b d, R s' b d -> R s b d \/ Issued w' b d) ->
  (forall b d, Issued w' b d -> tW w' < d -> Held w' b) ->
  (forall b d, Issued w b d -> Issued w' b d) -> bookingρ w' s'.
Proof.
move=> hρ hrec hres hret b d hR.
have hI : Issued w' b d by case: (hrec b d hR) => [/hρ[/hret]|].
by split=> //; exact: hres.
Qed.

(** **From a recorded confirmation to a held reservation** (App. E): with a
conservative clock in the correspondence ([t_W(w) ≤ t]), a recorded confirmation
that has not expired by the state's clock is held in the world. *)
Lemma booking_goal {w : Wb} {s : Sb} {b : Bk} {d t : nat} :
  bookingρ w s -> R s b d -> tW w <= t -> t < d -> Held w b.
Proof.
by move=> hρ hR hclock hexp; apply: (hρ b d hR).2; exact: leq_ltn_trans hexp.
Qed.

End Booking.

Arguments bookingρ {Bk Wb Sb} R Issued Held tW w s.
Arguments booking_correspondence {Bk Wb Sb} R Issued Held tW {w w' s s'}
  _ _ _ _.
Arguments booking_goal {Bk Wb Sb} R Issued Held tW {w s b d t} _ _ _ _.
