(** * The travel contract (Table 1) and the session of Fig. 2

The travel contract as a standard contract. The task part records the
commitments, the recipients of the passport, the bookings, the expert's ratings,
the mail read, the visa and the escrow; the passport itself is never part of
what the agent sees. Every episode of Fig. 2 is a checked statement: the calls
that are rejected have a false obligation, so no proof is accepted, whatever the
allowance; the calls that run have a proof, the one the agent submits. *)

From HB Require Import structures.
From Stdlib Require Import String.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Completion Standard.

Unset Printing Implicit Defensive.

Module Travel.

Import Standard.

(** Strings, with their decidable equality (local to the example). *)
HB.instance Definition _ := hasDecEq.Build string String.eqb_spec.

(** The visa; the consulate's decision is final. *)
Inductive Visa := VPending | Granted | Refused.

Definition visa_eqb (a b : Visa) : bool :=
  match a, b with
  | VPending, VPending | Granted, Granted | Refused, Refused => true
  | _, _ => false
  end.

Lemma visa_eqP : Equality.axiom visa_eqb.
Proof. by case=> -[]; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build Visa visa_eqP.

(** The escrow, held by the Airlock. *)
Inductive Escrow := Locked | Paid | Refunded.

Definition escrow_eqb (a b : Escrow) : bool :=
  match a, b with Locked, Locked | Paid, Paid | Refunded, Refunded => true
  | _, _ => false
  end.

Lemma escrow_eqP : Equality.axiom escrow_eqb.
Proof. by case=> -[]; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build Escrow escrow_eqP.

(** The task part of the travel contract: commitments, fees included; to whom
the passport was sent; bookings (hotel, night, amount); the expert's ratings, as
recorded (hotel, rating); the mail read (sender, body); the visa; the escrow. *)
Record X := MkX {
  spent : nat;
  discl : seq string;
  booked : seq (string * nat * nat);
  ratings : seq (string * nat);
  inbox : seq (string * string);
  visa : Visa;
  escrow : Escrow;
}.

(** Record updates. *)
Definition with_ratings (x : X) (rs : seq (string * nat)) : X :=
  MkX (spent x) (discl x) (booked x) rs (inbox x) (visa x) (escrow x).
Definition with_booking (x : X) (e : string * nat * nat) : X :=
  MkX (spent x + e.2) (discl x) (e :: booked x) (ratings x) (inbox x)
    (visa x) (escrow x).
Definition with_inbox (x : X) (new : seq (string * string)) : X :=
  MkX (spent x) (discl x) (booked x) (ratings x) (inbox x ++ new)
    (visa x) (escrow x).
Definition with_discl (x : X) (r : string) : X :=
  MkX (spent x) (r :: discl x) (booked x) (ratings x) (inbox x)
    (visa x) (escrow x).
Definition with_escrow (x : X) (e : Escrow) : X :=
  MkX (spent x) (discl x) (booked x) (ratings x) (inbox x) (visa x) e.

(** The first recorded rating of a hotel in a list of ratings, [0] if none. *)
Fixpoint lookup (h : string) (rs : seq (string * nat)) : nat :=
  match rs with
  | [::] => 0
  | (h', r) :: rs => if h' == h then r else lookup h rs
  end.

(** The recorded rating of a hotel, [0] if the expert was not asked. *)
Definition rating (x : X) (h : string) : nat := lookup h (ratings x).

(** The designated consulate. *)
Definition consulate : string := "consulate".

(** **The constraints at every instant** (Table 1): at most 2000 in commitments,
fees included; the passport only to the designated consulate; every booked hotel
with a recorded rating of at least 7. A decidable test. *)
Definition B (x : X) : bool :=
  [&& spent x <= 2000, all (pred1 consulate) (discl x) &
    all (fun e => 7 <= rating x e.1.1) (booked x)].

(** **The goal** (Table 1): confirmed bookings for nights 1–3, and a granted
visa. A decidable test. *)
Definition Goal (x : X) : bool :=
  all (fun n => has (fun e => e.1.2 == n) (booked x)) [:: 1; 2; 3] &&
    (visa x == Granted).

(** **Outside changes**: mail may arrive, and the consulate may decide on the
visa; nothing else changes. *)
Record Out (x x' : X) : Prop := MkOut {
  out_spent : spent x' = spent x;
  out_discl : discl x' = discl x;
  out_booked : booked x' = booked x;
  out_ratings : ratings x' = ratings x;
  out_escrow : escrow x' = escrow x;
  out_inbox : exists new, inbox x' = inbox x ++ new;
  out_visa : visa x = VPending \/ visa x' = visa x;
}.

Arguments out_spent {x x'} _.
Arguments out_discl {x x'} _.
Arguments out_booked {x x'} _.
Arguments out_ratings {x x'} _.
Arguments out_escrow {x x'} _.
Arguments out_inbox {x x'} _.
Arguments out_visa {x x'} _.

(** Outside changes, as a test. *)
Definition out (x x' : X) : bool :=
  [&& spent x' == spent x, discl x' == discl x, booked x' == booked x,
      ratings x' == ratings x
    & [&& escrow x' == escrow x, prefix (inbox x) (inbox x')
        & (visa x == VPending) || (visa x' == visa x)]].

Lemma outP (x x' : X) : reflect (Out x x') (out x x').
Proof.
apply: (iffP idP) => [|[hs hd hb hr he /prefixP hi hv]].
  case/and5P=> /eqP hs /eqP hd /eqP hb /eqP hr /and3P[/eqP he /prefixP hi hv].
  by split=> //; case/orP: hv => /eqP; [left | right].
rewrite /out hs hd hb hr he hi !eqxx /=.
by case: hv => ->; rewrite eqxx ?orbT.
Qed.

(** The tools of the task. *)
Inductive N := Rate | Book | DownloadMail | SendPassport.

(** Their inputs. *)
Definition inp (l : N) : Type :=
  match l with
  | Rate => string
  | Book => string * nat * nat
  | DownloadMail => unit
  | SendPassport => string
  end.

(** What each tool does to the task part, before the outside changes during the
call. *)
Definition eff (l : N) : inp l -> X -> X -> Prop :=
  match l return inp l -> X -> X -> Prop with
  | Rate => fun h x y => y = x \/
      (rating x h = 0 /\ h \notin unzip1 (ratings x) /\
       exists r, r <= 10 /\ y = with_ratings x ((h, r) :: ratings x))
  | Book => fun i x y => y = x \/ y = with_booking x i
  | DownloadMail => fun _ x y => exists new, y = with_inbox x new
  | SendPassport => fun r x y => y = x \/ y = with_discl x r
  end.

(** The task tools: [rate] (the expert, its answer recorded once), [book] (the
amount caps the charge, fees included), [download_mail], [sendPassport]; each
lasts at most a minute. *)
Definition tasks (l : N) : Task X :=
  MkTask (inp l) (fun i x x' => exists y, eff l i x y /\ out y x')
    (fun _ => 60).

(** The deadline: 30 days after signing, in seconds. *)
Definition deadline : nat := 30 * 24 * 3600.

(** Where control may start the contract. *)
Definition readyX (x : X) (t : nat) : bool :=
  [&& spent x == 0, nilp (discl x), nilp (booked x), escrow x == Locked
    & t + 60 <= deadline].

(** **The travel contract** (Table 1), as a standard contract. The agent sees
the whole task part (the passport's contents are not part of it); control checks
every minute, and terminates at the deadline or upon visa refusal, refunding the
escrow. *)
Definition spec : Spec X :=
  MkSpec X id B Goal deadline N tasks (fun x x' => x' = with_escrow x Paid)
    readyX (fun x x' => x' = x) 60 (fun x x' => x' = x) (fun x x' => out x x')
    60 (fun x => visa x == Refused) (fun x x' => x' = with_escrow x Refunded).

Lemma out_refl (x : X) : out x x.
Proof. by rewrite /out !eqxx prefix_refl orbT. Qed.

Lemma out_B {x x' : X} : B x -> out x x' -> B x'.
Proof.
by move=> hB /outP[hs hd hb hr _ _ _]; rewrite /B /rating hs hd hb hr.
Qed.

(** **The design obligations hold**, so the travel contract satisfies A3
([Spec.cert]). *)
Theorem design : Spec.Design spec.
Proof.
split.
- move=> x t x' t' /= /and5P[/eqP hs /nilP hd /nilP hb _ htd] -> ht.
  by rewrite /B hs hd hb (leq_trans ht htd).
- exact: out_refl.
- by move=> x x'; exact: out_B.
Qed.

(** The travel contract's certificate: A3. *)
Theorem cert : Contract.Cert (Spec.contract spec).
Proof. exact: Spec.cert spec design. Qed.

(** ** What each call asks *)

Lemma outStar_B {x x' : X} : B x -> Spec.OutStar spec x x' -> B x'.
Proof.
by move=> hB h; elim: h hB => // y z w _ ih ho hB; exact: out_B (ih hB) ho.
Qed.

Lemma outStar_fields {x x' : X} :
  Spec.OutStar spec x x' ->
  [/\ spent x' = spent x, discl x' = discl x, booked x' = booked x
    & ratings x' = ratings x].
Proof.
by elim=> // y z w _ [h1 h2 h3 h4] /outP[hs hd hb hr _ _ _];
  rewrite hs hd hb hr.
Qed.

Lemma outStar_goal {x x' : X} : Goal x -> Spec.OutStar spec x x' -> Goal x'.
Proof.
move=> hG h; elim: h hG => // y z w _ ih /outP[_ _ hb _ _ _ hv]
  /ih /andP[hbk /eqP hvis].
by rewrite /Goal hb hbk /=; case: hv => hv;
  [rewrite hvis in hv | rewrite hv hvis].
Qed.

Lemma rating_cons {x : X} {h h' : string} {r : nat} :
  h' <> h -> rating (with_ratings x ((h, r) :: ratings x)) h' = rating x h'.
Proof. by move=> hne; rewrite /rating /=; case: eqP => // heq; case: hne. Qed.

(** **The expert's answer is recorded** (memoization): asking again leaves a
recorded rating unchanged. *)
Theorem rate_memo {x x' : X} {h : string} :
  h \in unzip1 (ratings x) -> Dx (tasks Rate) h x x' ->
    rating x' h = rating x h.
Proof.
move=> hrated [y [hy /outP ho]]; have hr := out_ratings ho.
case: hy => [hyx|[_ [hnot _]]]; first by rewrite /rating hr hyx.
by rewrite hrated in hnot.
Qed.

Lemma rate_keeps_B {x x' : X} {h : string} :
  B x -> Dx (tasks Rate) h x x' -> B x'.
Proof.
move=> hB [y [hy ho]]; apply: out_B ho.
case: hy => [->|[h0 [_ [r [_ ->]]]]] //.
case/and3P: hB => h1 h2 /allP h3; rewrite /B /= h1 h2 /=; apply/allP => e he.
have hne : e.1.1 <> h by move=> heq; have := h3 e he; rewrite heq h0.
by rewrite rating_cons //; exact: h3.
Qed.

Lemma book_keeps_B {x x' : X} {h : string} {n m : nat} :
  B x -> spent x + m <= 2000 -> 7 <= rating x h ->
    Dx (tasks Book) (h, n, m) x x' -> B x'.
Proof.
move=> hB hm hr [y [hy ho]]; apply: out_B ho.
case: hy => [->|->] //.
by case/and3P: hB => _ h2 h3; rewrite /B /=; apply/and4P; split.
Qed.

Lemma download_keeps_B {x x' : X} :
  B x -> Dx (tasks DownloadMail) tt x x' -> B x'.
Proof.
by move=> hB [y [[new ->] ho]];
  exact: (out_B (x := with_inbox x new) hB ho).
Qed.

Lemma send_keeps_B {x x' : X} {r : string} :
  B x -> r = consulate -> Dx (tasks SendPassport) r x x' -> B x'.
Proof.
move=> hB -> [y [hy ho]]; apply: out_B ho.
by case: hy => [->|->].
Qed.

Lemma tasks_en (l : N) (i : Inp (tasks l)) (x : X) :
  exists x', Dx (tasks l) i x x'.
Proof.
case: l i => i; last 2 [by exists (with_inbox x [::]), (with_inbox x [::]);
  split; [exists [::] | exact: out_refl]].
all: by exists x, x; split; [left | exact: out_refl].
Qed.

(** Asking the expert is admissible at any compliant view, before the
deadline. *)
Theorem rate_ok {n t : nat} {x : X} (h : string) :
  t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask Rate) h)
    (x, t, Ongoing).
Proof.
move=> ht.
exact: (Spec.oblN_task spec design ht
  (fun _ _ _ _ _ _ hB₁ hd => rate_keeps_B hB₁ hd)
  (tasks_en Rate h)).
Qed.

(** Booking a hotel rated at least 7, within the budget, is admissible. *)
Theorem book_ok {n t : nat} {x : X} {h : string} {night m : nat} :
  spent x + m <= 2000 -> 7 <= rating x h -> t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask Book) (h, night, m))
    (x, t, Ongoing).
Proof.
move=> hm hr ht.
apply: (Spec.oblN_task spec design ht _ (tasks_en Book _)).
move=> y y₁ y₂ /= -> _ hout hB₁ hd.
have [hs _ _ hrt] := outStar_fields hout.
by apply: book_keeps_B hB₁ _ _ hd; rewrite ?hs // /rating hrt.
Qed.

(** Downloading mail is admissible at any compliant view, before the
deadline. *)
Theorem download_ok {n t : nat} {x : X} :
  t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask DownloadMail) tt)
    (x, t, Ongoing).
Proof.
move=> ht.
exact: (Spec.oblN_task spec design ht
  (fun _ _ _ _ _ _ hB₁ hd => download_keeps_B hB₁ hd)
  (tasks_en DownloadMail tt)).
Qed.

(** Sending the passport to the consulate is admissible. *)
Theorem send_ok {n t : nat} {x : X} :
  t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask SendPassport) consulate)
    (x, t, Ongoing).
Proof.
move=> ht.
exact: (Spec.oblN_task spec design ht
  (fun _ _ _ _ _ _ hB₁ hd => send_keeps_B hB₁ erefl hd)
  (tasks_en SendPassport consulate)).
Qed.

(** Settling once the goal holds is admissible: the goal survives outside
changes. *)
Theorem settle_ok {n t : nat} {x : X} :
  Goal x ->
  Contract.OblN (Spec.contract spec) n (existT _ NSettle tt) (x, t, Ongoing).
Proof.
move=> hG; apply: (Spec.oblN_settle spec design) => y y₁ /= -> _ hout.
exact: outStar_goal hG hout.
Qed.

(** ** The session of Fig. 2 *)

(** The hotels, and the address of the injected message. *)
Definition aurora : string := "Aurora".
Definition belvedere : string := "Belvedere".
Definition injected : string := "x@visa.io".

(** The task part at the start: nothing spent, sent or booked, no rating, no
mail, visa pending, escrow locked. *)
Definition x₀ : X := MkX 0 [::] [::] [::] [::] VPending Locked.

(** After the expert rated Belvedere 5 and Aurora 8. *)
Definition x₁ : X := with_ratings x₀ [:: (aurora, 8); (belvedere, 5)].

(** After booking Aurora for night 1 at 900. *)
Definition x₂ : X :=
  MkX 900 (discl x₁) [:: (aurora, 1, 900)] (ratings x₁) (inbox x₁)
    (visa x₁) (escrow x₁).

(** Once the three nights are booked, the passport sent to the consulate and the
visa granted. *)
Definition x₃ : X :=
  MkX 1900 [:: consulate]
    [:: (aurora, 3, 500); (aurora, 2, 500); (aurora, 1, 900)]
    (ratings x₂) (inbox x₂) Granted (escrow x₂).

Lemma B_x₀ : B x₀.
Proof. by []. Qed.

Lemma B_x₂ : B x₂.
Proof. by []. Qed.

(** **Episode 1.** Booking the partner hotel, which the expert has not rated,
has no proof, whatever the allowance. *)
Theorem ep1_book_rejected (n t : nat) : t <= deadline ->
  ~ Contract.OblN (Spec.contract spec) n
    (existT _ (NTask Book) (belvedere, 1, 260)) (x₀, t, Ongoing).
Proof.
move=> ht; apply: (Spec.not_oblN_task spec ht x₀
  (with_booking x₀ (belvedere, 1, 260)) erefl B_x₀).
  by exists (with_booking x₀ (belvedere, 1, 260)); split;
    [right | exact: out_refl].
by [].
Qed.

(** **Episode 1.** Asking the expert is admissible; asking again returns the
recorded rating. *)
Theorem ep1_rate (n t : nat) : t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask Rate) belvedere)
    (x₀, t, Ongoing).
Proof. exact: rate_ok. Qed.

Theorem ep1_rate_again {x' : X} :
  Dx (tasks Rate) belvedere x₁ x' -> rating x' belvedere = 5.
Proof.
by move=> hd; rewrite (rate_memo (x := x₁) (h := belvedere) (erefl true) hd).
Qed.

(** **Episode 2.** Booking Aurora, rated 8, for 900: the agent's proof. A policy
that capped each night at 600 would reject it, although it keeps the budget
([policy_engine_example]). *)
Theorem ep2_book (n t : nat) : t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask Book) (aurora, 1, 900))
    (x₁, t, Ongoing).
Proof. exact: book_ok. Qed.

(** **Episode 3.** Downloading the mail is admissible, whatever arrives; sending
the passport to the address of the injected message has no proof. *)
Theorem ep3_download (n t : nat) : t + n * 60 + 60 <= deadline ->
  Contract.OblN (Spec.contract spec) n (existT _ (NTask DownloadMail) tt)
    (x₂, t, Ongoing).
Proof. exact: download_ok. Qed.

Theorem ep3_injection_rejected (n t : nat) : t <= deadline ->
  ~ Contract.OblN (Spec.contract spec) n
    (existT _ (NTask SendPassport) injected) (x₂, t, Ongoing).
Proof.
move=> ht; apply: (Spec.not_oblN_task spec ht x₂ (with_discl x₂ injected)
  erefl B_x₂).
  by exists (with_discl x₂ injected); split; [right | exact: out_refl].
by [].
Qed.

(** **Episode 4.** Settling while the visa is pending has no proof; once the
goal holds, settling is admissible, and the escrow is released without further
approval. *)
Theorem ep4_premature (n t : nat) : t <= deadline ->
  ~ Contract.OblN (Spec.contract spec) n (existT _ NSettle tt) (x₂, t, Ongoing).
Proof. by move=> ht; apply: (Spec.not_oblN_settle spec ht x₂ erefl B_x₂). Qed.

Theorem ep4_settle (n t : nat) :
  Contract.OblN (Spec.contract spec) n (existT _ NSettle tt) (x₃, t, Ongoing).
Proof. exact: settle_ok. Qed.

End Travel.
