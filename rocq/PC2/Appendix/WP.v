(** * Appendix A: the obligation as a weakest precondition

What the agent knows, [K_n(v)]; Eq. (A.1); gates; Proposition A.1, the most
permissive safe gate; and the policy-engine example. *)

From Stdlib Require Import Lia.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat zify.
From PC2 Require Import Basic.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

Module ContractWP.

Section WP.

Variables (S : Type) (K : Contract S).

(** **What the agent knows** (App. A): the states it cannot rule out for a call
that may start after up to [n] control steps from a view [v]. *)
Definition Kn (n : nat) (v : V K) (s' : S) : Prop :=
  Active K s' /\ exists s, [/\ Active K s, view K s = v, C K s & Win K n s s'].

(** **Eq. (A.1)**: the delayed obligation is the weakest precondition of the
call for [C] at every state the agent cannot rule out. *)
Lemma oblN_wp (n : nat) (c : Call K) (v : V K) :
  OblN K n c v <-> forall s', Kn n v s' -> wp (D K c) (C K) s'.
Proof.
split=> [h s' [ha' [s [ha hv hc hw]]]|h s s' ha ha' hv hc hw];
  first exact: h hw.
by apply: h; split=> //; exists s.
Qed.

(** A gate decides, from a request and the view it is based on, whether the call
may run; it is **safe** if every call it admits is admissible at every state
from which it may start. *)
Definition SafeGate (G : Call K -> nat -> V K -> Prop) : Prop :=
  forall c n v, G c n v -> forall s', Kn n v s' -> Adm K c s'.

(** **Proposition A.1 (The most permissive safe gate).** The obligation is a
safe gate, and every safe gate implies it. *)
Lemma most_permissive_gate :
  SafeGate (fun c n v => OblN K n c v) /\
  forall G, SafeGate G -> forall c n v, G c n v -> OblN K n c v.
Proof.
split=> [c n v /oblN_wp //|G hG c n v hg].
by apply/oblN_wp; exact: hG hg.
Qed.

(** **Proposition A.1, second part.** A decidable safe gate that admitted every
call whose obligation holds would decide the obligation, [g] reflecting it:
where the obligations are undecidable, every decidable safe gate rejects some
call whose obligation holds. *)
Lemma decidable_gate (g : Call K -> nat -> V K -> bool)
    (hsafe : SafeGate (fun c n v => g c n v))
    (hall : forall c n v, OblN K n c v -> g c n v) :
  forall c n v, reflect (OblN K n c v) (g c n v).
Proof.
move=> c n v; apply: (iffP idP) => [|/hall //].
exact: most_permissive_gate.2 _ hsafe c n v.
Qed.

End WP.

Arguments Kn {S} K n v s'.
Arguments SafeGate {S} K G.
Arguments oblN_wp {S} K n c v.
Arguments most_permissive_gate {S} K.
Arguments decidable_gate {S} K g hsafe hall c n v.

End ContractWP.

(** **The policy-engine example** (App. A): a rule that caps each of three
nights at 600 keeps a budget of 2000, and rejects a first night at 900 followed
by two at 500, which keep the budget too. *)
Lemma policy_engine_example :
  (forall a b c : nat, a <= 600 -> b <= 600 -> c <= 600 -> a + b + c <= 2000) /\
  ~ (900 <= 600) /\ 900 + 500 + 500 <= 2000.
Proof.
by split=> [a b c ha hb hc|]; [lia | split].
Qed.
