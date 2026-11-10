(** * Anytime compliance (§4.1): Lemma 1 and Theorem 1

The proof follows the paper's. Between operations, the variables satisfy an
invariant: once the contract has started, the certificate holds (it was checked
at startup, A1), the record complies, and each view published since the last
call was computed from a compliant active state whose window reaches the record.
A control step is then admissible by A3; a call, by its accepted obligation (A1)
applied through the Window lemma; and by A2 every instant of an operation is in
its model. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

Section Compliance.

Variables (S : Type) (K : Contract S) (P W : Type) (ch : Checker P) (πK : P)
  (E : Effects K W).

(** The invariant between operations. *)
Record Inv (x : Vars K P) : Prop := {
  inv_wf : Wf K ch x;
  inv_cert : phase x <> Init -> Cert K;
  inv_comp : phase x <> Init -> Active K (record x) -> C K (record x);
  inv_views : phase x = Top -> Active K (record x) ->
    forall (j : nat) (v₀ : V K),
    ltl (klast x) j -> onth (views x) j = Some v₀ ->
    exists r, [/\ view K r = v₀, Active K r, C K r
      & Win K (kcur x - j) r (record x)];
}.

Lemma inv_start (s₀ : S) : Inv (start K s₀).
Proof. by split=> //; exact: wf_start. Qed.

(** **Lemma 1 (Window).** Let a call run for the request [(T, i, k₀, n, π)] from
the record, at the start of an iteration [k], with no call since the view [v₀ =
v[k₀]] was published ([kLast < k₀]) and [k ≤ k₀ + n]. If the clause has held so
far (the invariant), then the state [sv] from which [v₀] was computed and the
record are active, [sv] complies, and the record is in the window of [sv]:
[D^{≤n}_ctrl(sv, record)]. *)
Lemma window {x : Vars K P} {q : Request K P} {v₀ : V K} :
  Inv x -> phase x = Top -> Active K (record x) -> ltl (klast x) (k₀ q) ->
  kcur x <= k₀ q + allow q -> onth (views (publish x)) (k₀ q) = Some v₀ ->
  exists sv, [/\ view K sv = v₀, Active K sv, C K sv
    & Win K (allow q) sv (record x)].
Proof.
move=> hI hx ha hlast hk.
have hc : C K (record x) by apply: inv_comp hI _ ha; rewrite hx.
rewrite /= onth_rcons; case: ltnP => [_ hv|_].
  have [r [hr hra hrc hw]] := inv_views hI hx ha _ hlast hv.
  by exists r; split=> //; apply: win_mono hw; rewrite leq_subLR.
by case: eqP => // _ [<-]; exists (record x); split=> //; exact: win_refl.
Qed.

(** Under A1, an operation that Algorithm 1 invokes is enabled where it starts,
and every state its model admits complies; during initialization, every active
one. *)
Lemma next_safe (hA1 : Checker.Sound ch) {x : Vars K P} {inp : Input K P}
    {o : Op K P} {κ : S -> Vars K P} :
  Inv x -> Next K ch πK x inp o κ ->
  (exists s', model o (record x) s') /\
  forall s', model o (record x) s' ->
    (phase x <> Init \/ Active K s') -> C K s'.
Proof.
move=> hI h; case: h (h) hI => {}x;
  [| | move=> x₂ {}inp hx ha _ _ _ hI | move=> {}inp hx ha _ hI].
- move=> {}inp hx hacc hin _ hI; have hK : Cert K := hA1 _ _ hacc.
  split; first exact: (enabled hK hin).
  by move=> s' hs [hne|ha'];
    [rewrite hx in hne | exact: (initializer hK hin ha' hs)].
- move=> x₂ {}inp q _ _ _ _ _ _ hN hI.
  have [hx ha /checkOKP[hlast /andP[_ hk] [v₀ hv hacc]]] :=
    call_facts (inv_wf hI) hN.
  have [sv [hvs has hcs hw]] := window hI hx ha hlast hk hv.
  have [hen hall] := hA1 _ _ hacc sv (record x) has ha hvs hcs hw.
  by split=> // s' hs _; exact: hall.
all: have hne : phase x <> Init by rewrite hx.
all: have [hen hall] := controller (inv_cert hI hne) ha (inv_comp hI hne ha).
all: by split=> // s' hs _; exact: hall.
Qed.

(** After an operation, the phase is never [Init]. *)
Lemma next_phase {x : Vars K P} {inp : Input K P} {o : Op K P}
  {κ : S -> Vars K P} :
  Next K ch πK x inp o κ -> forall s, phase (κ s) <> Init.
Proof.
case=> //= {}x x₂ {}inp hx _ hc _ s.
by case: (step_eq hc) => rq [r ->]; rewrite /= hx.
Qed.

(** Under A1, the invariant holds after an operation whose reading its model
admits. *)
Lemma next_inv (hA1 : Checker.Sound ch) {x : Vars K P} {inp : Input K P}
    {o : Op K P} {κ : S -> Vars K P} {s : S} :
  Inv x -> Next K ch πK x inp o κ -> model o (record x) s -> Inv (κ s).
Proof.
move=> hI h hs.
have hsafe := next_safe hA1 hI h.
have hwf := wf_next (s := s) (inv_wf hI) h.
case: h hI hsafe hwf hs => {}x.
- move=> {}inp hx hacc hin hI hsafe hwf hs; split=> //= [_|_ ha'|_ _ j v₀ _].
  + exact: hA1 _ _ hacc.
  + exact: hsafe.2 s hs (or_intror ha').
  + by have [-> _] := wf_init (inv_wf hI) hx; rewrite onth0n.
- move=> x₂ {}inp q hx _ _ _ _ _ hI hsafe hwf hs.
  have hne : phase x <> Init by rewrite hx.
  split=> //= [_|_ _]; first exact: inv_cert hI hne.
  exact: hsafe.2 s hs (or_introl hne).
- move=> x₂ {}inp hx ha hc _ hI hsafe hwf hs.
  have hne : phase x <> Init by rewrite hx.
  case: (step_eq hc) => rq [r ex₂]; subst x₂.
  split=> //= [_|_ _|_ _ j v₀ hlast]; first exact: inv_cert hI hne.
    exact: hsafe.2 s hs (or_introl hne).
  have hlen := wf_top (inv_wf hI) hx.
  have hcx := inv_comp hI hne ha.
  rewrite onth_rcons; case: ltnP => [hlt hv|_].
    have [r' [hr hra hrc hw]] := inv_views hI hx ha _ hlast hv.
    have hj : j <= kcur x by rewrite -hlen ltnW.
    by exists r'; split=> //; rewrite subSn //; exact: win_snoc hw ha hs.
  case: eqP => // -> [<-]; exists (record x); split=> //.
  by rewrite hlen subSnn; exact: win_ctrl ha hs.
- move=> {}inp hx ha hI hsafe hwf hs.
  have hne : phase x <> Init by rewrite hx.
  split=> //= [_|_ _|_ _ j v₀ hlast hv]; first exact: inv_cert hI hne.
    exact: hsafe.2 s hs (or_introl hne).
  have [hlen hkl _] := wf_after (inv_wf hI) hx.
  have hj : j < size (views x) by rewrite -onthTE hv.
  by move: hlast; rewrite hkl /= ltnNge -ltnS -hlen hj.
Qed.

(** The clause at every instant of an operation from the start of the contract:
at every instant of an operation after the first, and at every active instant of
the first, the initialization. *)
Definition SegCompliant (j : nat) (σ : Segment W S) : Prop :=
  forall τ : Inst σ, (0 < j \/ Active K (pt σ τ).2) -> C K (pt σ τ).2.

(** The clause at every instant of every operation of a list, from the start of
the contract. *)
Definition Compliant (xs : seq (Op K P * Segment W S)) : Prop :=
  forall j p, onth xs j = Some p -> SegCompliant j p.2.

Lemma compliant_append {xs : seq (Op K P * Segment W S)}
  {a : Op K P * Segment W S} :
  Compliant xs -> SegCompliant (size xs) a.2 -> Compliant (rcons xs a).
Proof. by move=> h₁ h₂; apply: onth_rcons_all. Qed.

(** An operation that Algorithm 1 invokes, whose instants are effects from the
record: under A1 and A2, the clause holds at each of its instants, from the
start of the contract. *)
Lemma segment_compliant (hA1 : Checker.Sound ch) (hA2 : Coverage K E) {w : W}
    {x : Vars K P} {inp : Input K P} {o : Op K P} {κ : S -> Vars K P}
    {j : nat} :
  Inv x -> (0 < j -> phase x <> Init) -> Next K ch πK x inp o κ ->
  forall σ : Segment W S,
    (forall τ, Effects.op E o w (record x) (pt σ τ).1 (pt σ τ).2) ->
  SegCompliant j σ.
Proof.
move=> hI hj h σ he τ hor.
have [hen hall] := next_safe hA1 hI h.
by apply: hall _ (coverage_op hA2 hen (he τ)) _;
  case: hor => [/hj|]; [left | right].
Qed.

(** Every execution keeps the invariant, starts with the initialization, and
complies, under A1 and A2. *)
Lemma exec_inv (hA1 : Checker.Sound ch) (hA2 : Coverage K E) {s₀ : S} {w : W}
    {x : Vars K P} {xs : seq (Op K P * Segment W S)} :
  Exec K ch πK E s₀ w x xs ->
  [/\ Inv x, phase x = Init <-> xs = [::] & Compliant xs].
Proof.
elim=> [w₀|{}w {}x {}xs inp o κ σ l _ [hI hph hC] hn _ he].
  by split; [exact: inv_start | by [] | move=> j p; rewrite onth0n].
have [hen _] := next_safe hA1 hI hn.
have hj : 0 < size xs -> phase x <> Init
  by move=> hpos /hph.1 h0; rewrite h0 in hpos.
split; first exact: (next_inv hA1 hI hn (coverage_op hA2 hen (he l))).
  by split=> [/(next_phase hn) //|/(congr1 size)]; rewrite size_rcons.
by apply: compliant_append hC _;
  exact: (segment_compliant hA1 hA2 hI hj hn σ he).
Qed.

(** Once an execution has an operation, the Airlock is past its
initialization. *)
Lemma exec_started (hA1 : Checker.Sound ch) (hA2 : Coverage K E) {s₀ : S}
    {w : W} {x : Vars K P} {xs : seq (Op K P * Segment W S)} :
  Exec K ch πK E s₀ w x xs -> 0 < size xs -> phase x <> Init.
Proof.
by move=> /(exec_inv hA1 hA2)[_ hph _] hpos /hph.1 h0; rewrite h0 in hpos.
Qed.

(** **Theorem 1 (Anytime compliance to the contract).** Under A1 (sound
checking) and A2 (coverage), for any sequence of requests and proposed proofs,
every execution of Algorithms 1–2 (A4) satisfies the clause at every instant of
every operation from the start of the contract: at every instant of the
operations after the initialization, and at every active instant of the
initialization, closing included, and throughout an operation that never
returns. A3 is not a hypothesis: the Airlock starts only once the checker has
accepted the certificate as a proof of it. *)
Theorem anytime_compliance (hA1 : Checker.Sound ch) (hA2 : Coverage K E)
    {s₀ : S} {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    (0 < j \/ Active K (pt p.2 τ).2) -> C K (pt p.2 τ).2.
Proof.
case=> [w x {}xs hx|w x {}xs inp o κ σ hx hn _ he];
  first by case: (exec_inv hA1 hA2 hx).
have [hI _ hC] := exec_inv hA1 hA2 hx.
apply: compliant_append hC _.
exact: (segment_compliant hA1 hA2 hI (exec_started hA1 hA2 hx) hn σ he).
Qed.

End Compliance.

Arguments Inv {S} K {P} ch x.
Arguments SegCompliant {S} K {W} j σ.
Arguments Compliant {S} K {P W} xs.
Arguments inv_start {S K P ch} s₀.
Arguments window {S K P ch x q v₀} _ _ _ _ _ _.
Arguments next_safe {S K P ch πK} hA1 {x inp o κ} _ _.
Arguments next_phase {S K P ch πK x inp o κ} _ s.
Arguments next_inv {S K P ch πK} hA1 {x inp o κ s} _ _ _.
Arguments compliant_append {S K P W xs a} _ _.
Arguments segment_compliant {S K P W ch πK E} hA1 hA2 {w x inp o κ j} _ _ _ σ _.
Arguments exec_inv {S K P W ch πK E} hA1 hA2 {s₀ w x xs} _.
Arguments exec_started {S K P W ch πK E} hA1 hA2 {s₀ w x xs} _ _.
Arguments anytime_compliance {S K P W ch πK E} hA1 hA2 {s₀ xs} _ j p _ τ _.
