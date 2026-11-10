(** * Executions (§4.1): effects, coverage, and A4

What happens when the Airlock invokes a routine is described by the **effects**
[Ê] of the deployment: from a world and a state, the world–state pairs an
invocation can reach at any instant of its execution, outside changes included
(§5.1). Their projection on states is [E] (§4.1). Coverage (A2) asks each model
to contain the states that execution can reach where the call is enabled.

An **execution** is a run of Algorithms 1–2 in which each operation is a segment
of time: the world and the state at each of its instants. A4 is the statement
that the actual execution of a deployment is one of these: (i) every segment
starts where the previous one ended, the first at the initial reading; (ii) the
reading after an operation is the state at the instant it returns; (iii) the
operations are those Algorithms 1–2 choose. That every instant from the start
belongs to some operation is also A4 (i); App. D shows how to make it true when
the host takes time between routines.

Instants are abstract: a segment has its own type of instants (an interval of
real time, ticks, anything), and no property of time is used. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

Module Effects.

(** The effects [Ê] of a deployment: [ecall c w s w' s'] holds when an
invocation of the call [c] starting in the world [w] and the state [s] can reach
[(w', s')] at some instant of its execution; [ectrl] likewise for the control
routine. *)
Record t (S : Type) (K : Contract S) (W : Type) := Build {
  ecall : Call K -> W -> S -> W -> S -> Prop;
  ectrl : W -> S -> W -> S -> Prop;
}.

Section Effects.

Variables (S : Type) (K : Contract S) (W : Type) (E : t K W).

(** The effects of an operation. *)
Definition op {P : Type} (o : Op K P) : W -> S -> W -> S -> Prop :=
  match o with OpCtrl => ectrl E | OpCall q => ecall E (call q) end.

(** [E_T], the projection of [Ê_T] on states (Eq. world-projection), for a
call. *)
Definition callE (c : Call K) (s s' : S) : Prop :=
  exists w w', ecall E c w s w' s'.

(** [E_ctrl], the projection of [Ê_ctrl] on states. *)
Definition ctrlE (s s' : S) : Prop := exists w w', ectrl E w s w' s'.

End Effects.

Arguments op {S K W} E {P} o _ _ _ _.
Arguments callE {S K W} E c s s'.
Arguments ctrlE {S K W} E s s'.

End Effects.

Abbreviation Effects := Effects.t.

(** **A2 (Coverage of state transitions).** Where a call or the control step is
enabled, its model contains every state its execution can reach. *)
Record Coverage (S : Type) (K : Contract S) (W : Type) (E : Effects K W) :
  Prop := {
  cov_call : forall (c : Call K) (s s' : S),
    (exists s'', D K c s s'') -> Effects.callE E c s s' -> D K c s s';
  cov_ctrl : forall (s s' : S),
    (exists s'', ctrl K s s'') -> Effects.ctrlE E s s' -> ctrl K s s';
}.

Arguments Coverage {S} K {W} E.

Lemma coverage_op {S : Type} {K : Contract S} {W P : Type} {E : Effects K W}
    (h : Coverage K E) {o : Op K P} {w w' : W} {s s' : S} :
  (exists s'', model o s s'') -> Effects.op E o w s w' s' -> model o s s'.
Proof.
by case: o => [|q] hen he; [apply: (cov_ctrl h hen) | apply: (cov_call h hen)];
  exists w, w'.
Qed.

(** An operation as it happens: the world and the state at each of its instants,
from its first. *)
Record Segment (W S : Type) := MkSegment {
  Inst : Type;
  pt : Inst -> W * S;
  first : Inst;
}.

Section Exec.

Variables (S : Type) (K : Contract S) (P W : Type) (ch : Checker P) (πK : P)
  (E : Effects K W).

(** **Executions of the Airlock (A4)**, from the reading [s₀]. Each operation
that Algorithms 1–2 choose, for the agent's input, is a segment that starts at
the current world and record (i), whose instants are effects of the operation
from there, and whose return gives the next reading (ii). The indices are the
world and the variables when the last operation returned, and the operations so
far, each with its segment. *)
Inductive Exec (s₀ : S) : W -> Vars K P -> seq (Op K P * Segment W S) -> Prop :=
  | exec_start (w₀ : W) : Exec s₀ w₀ (start K s₀) [::]
  | exec_step (w : W) (x : Vars K P) (xs : seq (Op K P * Segment W S))
    (inp : Input K P) (o : Op K P) (κ : S -> Vars K P) (σ : Segment W S)
    (l : Inst σ) :
      Exec s₀ w x xs -> Next K ch πK x inp o κ ->
      pt σ (first σ) = (w, record x) ->
      (forall τ, Effects.op E o w (record x) (pt σ τ).1 (pt σ τ).2) ->
      Exec s₀ (pt σ l).1 (κ (pt σ l).2) (rcons xs (o, σ)).

(** **An execution**: the operations that returned, possibly followed by one
more that is still running, or never returns. *)
Inductive Execution (s₀ : S) : seq (Op K P * Segment W S) -> Prop :=
  | returned (w : W) (x : Vars K P) (xs : seq (Op K P * Segment W S)) :
      Exec s₀ w x xs -> Execution s₀ xs
  | running (w : W) (x : Vars K P) (xs : seq (Op K P * Segment W S))
    (inp : Input K P) (o : Op K P) (κ : S -> Vars K P) (σ : Segment W S) :
      Exec s₀ w x xs -> Next K ch πK x inp o κ ->
      pt σ (first σ) = (w, record x) ->
      (forall τ, Effects.op E o w (record x) (pt σ τ).1 (pt σ τ).2) ->
      Execution s₀ (rcons xs (o, σ)).

(** The variables of an execution are reached by Algorithm 1. *)
Lemma exec_reach {s₀ : S} {w : W} {x : Vars K P}
    {xs : seq (Op K P * Segment W S)} :
  Exec s₀ w x xs -> Reach K ch πK s₀ x.
Proof.
by elim=> [w₀|{}w {}x {}xs inp o κ σ l _ ih hn _ _];
  [exact: reach_start | exact: reach_step ih hn].
Qed.

End Exec.

Arguments Exec {S} K {P W} ch πK E s₀ _ _ _.
Arguments Execution {S} K {P W} ch πK E s₀ _.
Arguments exec_start {S K P W ch πK E s₀} w₀.
Arguments exec_step {S K P W ch πK E s₀ w x xs inp o κ} σ l _ _ _ _.
Arguments returned {S K P W ch πK E s₀ w x xs} _.
Arguments running {S K P W ch πK E s₀ w x xs inp o κ} σ _ _ _ _.
Arguments exec_reach {S K P W ch πK E s₀ w x xs} _.
