(** * Appendix D: time between operations

A gap of at most [t₀] after each routine is included in the operation: the
extended tool [T'] runs the routine, then waits, and its model is [D_T'(i, s,
s'') = ∃ z, D_T(i, s, z) ∧ D_idle(t₀, z, s'')] (Eq. extended-model). The
extended contract [𝒦'] is a contract, so every result of the paper applies to
it, with its own assumptions. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From PC2 Require Import Basic.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** The extended tool [T'], for the model [gap] of what outside changes can do
within [t₀]. *)
Definition extend {S : Type} (T : Tool S) (gap : S -> S -> Prop) : Tool S :=
  @Tool.Build S (Tool.Inp T)
    (fun i s s'' => exists z, Tool.D T i s z /\ gap z s'').

(** The extended contract [𝒦']: the tools and the control step extended by the
gap. *)
Definition extendK {S : Type} (K : Contract S) (gap : S -> S -> Prop) :
    Contract S :=
  @Contract.Build S (Contract.C K) (Contract.V K) (Contract.view K)
    (Contract.Name K) (fun l => extend (Contract.tools K l) gap)
    (fun s s'' => exists z, Contract.ctrl K s z /\ gap z s'') (Contract.stop K).

Section Gaps.

Variables (S : Type) (T : Tool S) (gap : S -> S -> Prop).

(** The model of [T'] admits every state the model of [T] admits (the gap may be
zero). *)
Lemma extend_mono (hrefl : forall z, gap z z) {i : Tool.Inp T} {s s' : S} :
  Tool.D T i s s' -> Tool.D (extend T gap) i s s'.
Proof. by move=> h; exists s'. Qed.

(** [T'] is enabled exactly where [T] is. *)
Lemma extend_en (hrefl : forall z, gap z z) (i : Tool.Inp T) (s : S) :
  Tool.En (extend T gap) i s <-> Tool.En T i s.
Proof.
by split=> [[_ [z [hz _]]]|[z hz]]; [exists z | exists z, z].
Qed.

(** [(T|Pre)' = T'|Pre]: a goal-gated settlement stays goal-gated. *)
Lemma extend_restrict (Pre : Tool.Inp T -> pred S) (i : Tool.Inp T)
    (s s'' : S) :
  Tool.D (extend (Tool.restrict T Pre) gap) i s s'' <->
  Tool.D (Tool.restrict (extend T gap) Pre) i s s''.
Proof.
by split=> [[z [[hp hz] hg]]|[hp [z [hz hg]]]];
  [split=> //; exists z | exists z].
Qed.

(** With no gap ([t₀ = 0], the gap model is the identity), [T' = T]. *)
Lemma extend_zero (hid : forall z s'', gap z s'' <-> z = s'') (i : Tool.Inp T)
    (s s'' : S) :
  Tool.D (extend T gap) i s s'' <-> Tool.D T i s s''.
Proof.
split=> [[z [hz /hid <-]] //|h].
by exists s''; split=> //; apply/hid.
Qed.

End Gaps.

Arguments extend_mono {S T gap} hrefl {i s s'} _.
