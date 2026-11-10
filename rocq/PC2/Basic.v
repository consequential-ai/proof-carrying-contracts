(** * The formal core (§3): tools, contracts, obligations, the certificate

Definitions 1–4 of the paper, admissibility (Eqs. 1–3) as a weakest precondition
(App. A), the precondition construction (§3.5.2), and A3 as the statement of the
certificate the Airlock checks before it starts (Algorithm 1, line 2).

A predicate on [X] is a function [X -> Prop], a relation a function [X -> Y ->
Prop]; a decidable test is a function to [bool], used as a predicate through
[is_true]. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** ** Sequences: [onth] after [rcons] *)

Section Onth.

Variable A : Type.
Implicit Types (l : seq A) (a b : A).

Lemma onth_rcons l a j :
  onth (rcons l a) j =
    if j < size l then onth l j else if j == size l then Some a else None.
Proof.
rewrite -cats1 onth_cat; case: ltngtP => // [hgt|->]; last by rewrite subnn.
by rewrite onth_default //= subn_gt0.
Qed.

Lemma onth_rcons_lt l a b j : onth l j = Some b -> onth (rcons l a) j = Some b.
Proof. by move=> h; rewrite onth_rcons -onthTE h. Qed.

(** The last element of [rcons l a] is [a]. *)
Lemma onth_rcons_size l a : onth (rcons l a) (size l) = Some a.
Proof. by rewrite onth_rcons ltnn eqxx. Qed.

(** A property of every element of a list, extended to one more element at its
end. *)
Lemma onth_rcons_all (Q : nat -> A -> Prop) l a :
  (forall j b, onth l j = Some b -> Q j b) -> Q (size l) a ->
  forall j b, onth (rcons l a) j = Some b -> Q j b.
Proof.
move=> h₁ h₂ j b; rewrite onth_rcons; case: ltnP => [_ /h₁ //|_].
by case: eqP => // -> [<-].
Qed.

End Onth.

Arguments onth_rcons_lt {A l a b j} _.
Arguments onth_rcons_all {A} Q {l a} _ _ _ _ _.

(** The relational weakest precondition (App. A): from [s], the relation [R]
admits some outcome, and every outcome satisfies [Q]. *)
Definition wp {S : Type} (R : S -> S -> Prop) (Q : S -> Prop) (s : S) : Prop :=
  (exists s', R s s') /\ forall s', R s s' -> Q s'.

(** A weakest precondition computed through an equivalent description of the
relation. *)
Lemma wp_of_iff {S : Type} {R : S -> S -> Prop} {Q : S -> Prop} {s : S}
    {R' : S -> Prop} :
  (forall s', R s s' <-> R' s') ->
  (exists s', R' s') /\ (forall s', R' s' -> Q s') -> wp R Q s.
Proof.
move=> hR [[s' hs'] hall]; split; first by exists s'; apply/hR.
by move=> s'' /hR; exact: hall.
Qed.

(** ** Tools (§3.1) *)

Module Tool.

(** **Definition 1 (Tool).** An input space [I_T] and a transition model [D_T]:
[D i s s'] holds for every state [s'] the model admits during an invocation on
[i] from [s], its initial, intermediate and final states, outside changes
included. The execution routine [exec_T] is not a mathematical object: what it
does enters through the effects of a deployment ([Effects]). *)
Record t (S : Type) := Build {
  Inp : Type;
  D : Inp -> S -> S -> Prop;
}.

Section Tool.

Variable S : Type.
Implicit Type T : t S.

(** Enabledness [Ξ_T(i,s)] (Eq. 2): the model admits some state. *)
Definition En T (i : Inp T) (s : S) : Prop := exists s', D T i s s'.

(** Daemonic control [Θ_T(i,s)] (Eq. 1): every state the model admits satisfies
[C]. *)
Definition Dem T (C : S -> Prop) (i : Inp T) (s : S) : Prop :=
  forall s', D T i s s' -> C s'.

(** Admissibility [𝒜_T(i,s)] (Eq. 3), the weakest precondition of the model for
[C]. *)
Definition Adm T (C : S -> Prop) (i : Inp T) (s : S) : Prop := wp (D T i) C s.

(** [𝒜_T = Ξ_T ∧ Θ_T], by definition. *)
Lemma adm_iff T (C : S -> Prop) (i : Inp T) (s : S) :
  Adm T C i s <-> En T i s /\ Dem T C i s.
Proof. by []. Qed.

(** **The precondition construction** [T|_Pre] (§3.5.2): same input and routine,
the model restricted to the starting states where [Pre] holds. *)
Definition restrict T (Pre : Inp T -> S -> Prop) : t S :=
  @Build S (Inp T) (fun i s s' => Pre i s /\ D T i s s').

(** [Ξ_{T|Pre}(i,s) ⟺ Pre(i,s) ∧ Ξ_T(i,s)] (§3.5.2). *)
Lemma en_restrict T (Pre : Inp T -> S -> Prop) (i : Inp T) (s : S) :
  En (restrict T Pre) i s <-> Pre i s /\ En T i s.
Proof.
by split=> [[s' [hp hd]]|[hp [s' hd]]]; [split=> //; exists s' | exists s'].
Qed.

(** Under a precondition, admissibility is the precondition and the original
admissibility; this is the obligation of Eq. (precondition-obligation) at each
state (§3.5.2). *)
Lemma adm_restrict T (C : S -> Prop) (Pre : Inp T -> S -> Prop) (i : Inp T)
    (s : S) :
  Adm (restrict T Pre) C i s <-> Pre i s /\ Adm T C i s.
Proof.
split=> [[[s' [hp hd]] hall]|[hp [[s' hd] hall]]].
  by split=> //; split=> [|s'' hd']; [exists s' | exact: hall].
by split=> [|s'' [_ hd']]; [exists s' | exact: hall].
Qed.

End Tool.

Arguments En {S} T i s.
Arguments Dem {S} T C i s.
Arguments Adm {S} T C i s.
Arguments restrict {S} T Pre.

End Tool.

Abbreviation Tool := Tool.t.

(** ** Contracts (§3.2) *)

Module Contract.

(** **Definition 2 (Contract)** [𝒦 = (Σ, C, View, 𝒯, ctrl, stop)], with [Σ] the
type [S]: the clause [C], the view, the tools available to the agent ([tools],
by name), the model of the control tool ([ctrl], which has no input and is
reserved for the Airlock), and the decidable inactivity test [stop]. A contract
fixes no initial state. *)
Record t (S : Type) := Build {
  C : S -> Prop;
  V : Type;
  view : S -> V;
  Name : Type;
  tools : Name -> Tool S;
  ctrl : S -> S -> Prop;
  stop : S -> bool;
}.

Section Contract.

Variables (S : Type) (K : t S).

(** The active states [Σ_act]; the others, where [stop K s] holds, are the
inactive states [Σ_stop]. *)
Definition Active (s : S) : bool := ~~ stop K s.

(** A call: a tool of the contract and an input of it. *)
Definition Call := {l : Name K & Tool.Inp (tools K l)}.

(** The model of a call. *)
Definition D (c : Call) : S -> S -> Prop :=
  Tool.D (tools K (projT1 c)) (projT2 c).

(** Admissibility of a call at a state (Eq. 3). *)
Definition Adm (c : Call) (s : S) : Prop := wp (D c) (C K) s.

(** ** Obligations (§3.3) *)

(** **Definition 3 (Obligation)** [Obl_T(i,v)]: the call is admissible at every
compliant active state with the view [v]. *)
Definition Obl (c : Call) (v : V K) : Prop :=
  forall s, Active s -> view K s = v -> C K s -> Adm c s.

(** The window [D^{≤n}_ctrl] (Eq. delayed-control): at most [n] control steps,
through active states. As in the paper it is cumulative: a window contains the
shorter ones. *)
Fixpoint Win (n : nat) (s s' : S) : Prop :=
  match n with
  | 0 => s = s'
  | n.+1 => Win n s s' \/ exists u, [/\ Active u, Win n s u & ctrl K u s']
  end.

(** **Definition 4 (Delayed obligation)** [Obl^{≤n}_T(i,v)]: the call is
admissible at every active state in the window of every compliant active state
with the view [v]. *)
Definition OblN (n : nat) (c : Call) (v : V K) : Prop :=
  forall s s', Active s -> Active s' -> view K s = v -> C K s ->
    Win n s s' -> Adm c s'.

(** **A3 (Initialization and control)**, as the statement of the certificate
[π_𝒦] that the Airlock checks before it starts (Algorithm 1, line 2). *)
Record Cert : Prop := {
  (** The controller line: from a compliant active state, control is
      admissible. *)
  controller : forall {s}, Active s -> C K s -> wp (ctrl K) (C K) s;
  (** The initializer line: from an inactive state, control makes the contract
  active only in [C]. *)
  initializer : forall {s s'}, stop K s -> Active s' -> ctrl K s s' -> C K s';
  (** Control is enabled at every inactive state. *)
  enabled : forall {s}, stop K s -> exists s', ctrl K s s';
}.

(** With no control step, the delayed obligation is the obligation (§3.3). *)
Lemma oblN_zero (c : Call) (v : V K) : OblN 0 c v <-> Obl c v.
Proof.
split=> [h s ha hv hc | h s s' ha _ hv hc hw];
  first exact: (h s s ha ha hv hc (erefl s)).
by rewrite /= in hw; subst s'; exact: h.
Qed.

(** A longer window contains a shorter one. *)
Lemma win_mono {m n : nat} {s s' : S} : m <= n -> Win m s s' -> Win n s s'.
Proof.
elim: n => [|n ih]; first by rewrite leqn0 => /eqP ->.
by rewrite leq_eqVlt => /predU1P[-> //|hlt hw]; left; exact: ih.
Qed.

(** Every window contains its starting state. *)
Lemma win_refl {n : nat} {s : S} : Win n s s.
Proof. exact: win_mono (leq0n n) (erefl s). Qed.

(** One more control step, from an active state, extends a window. *)
Lemma win_snoc {n : nat} {s u s' : S} :
  Win n s u -> Active u -> ctrl K u s' -> Win n.+1 s s'.
Proof. by move=> hw hu hc; right; exists u. Qed.

(** A single control step, from an active state, is a window of one step. *)
Lemma win_ctrl {u s' : S} : Active u -> ctrl K u s' -> Win 1 u s'.
Proof. by move=> hu hc; right; exists u. Qed.

(** Under A3, the states of a window of a compliant state comply. *)
Lemma win_C (hK : Cert) {n : nat} {s s' : S} : C K s -> Win n s s' -> C K s'.
Proof.
move=> hc; elim: n s' => [|n ih] s' /=; first by move=> <-.
case=> [|[u [hu hw hc']]]; first exact: ih.
exact: (controller hK hu (ih _ hw)).2.
Qed.

(** The delayed obligation is antitone in the allowance. *)
Lemma oblN_mono {m n : nat} {c : Call} {v : V K} :
  m <= n -> OblN n c v -> OblN m c v.
Proof. by move=> hmn h s s' ha ha' hv hc /(win_mono hmn); exact: h. Qed.

End Contract.

Arguments Active {S} K s.
Arguments D {S} K c _ _.
Arguments Adm {S} K c s.
Arguments Obl {S} K c v.
Arguments Win {S} K n s s'.
Arguments OblN {S} K n c v.
Arguments Cert {S} K.
Arguments oblN_zero {S K} c v.
Arguments win_mono {S K m n s s'} _ _.
Arguments win_refl {S K n s}.
Arguments win_snoc {S K n s u s'} _ _ _.
Arguments win_ctrl {S K u s'} _ _.
Arguments win_C {S K} hK {n s s'} _ _.
Arguments oblN_mono {S K m n c v} _ _.

End Contract.

Abbreviation Contract := Contract.t.
