(** * Algorithms 1–2 as programs (Rocq only)

[Airlock] specifies Algorithm 1, with the proof checking of Algorithm 2, as
relations: [Next] for an iteration of the loop, [Run] for the runs. This file
implements them as Rocq functions, [step] and [run], and proves that the
functions implement the relations ([nextP], [run_sound], [run_complete],
[reach_run]).

Besides the agent's input, [Next] leaves two things open, and the functions take
both as inputs: how far the parallel check has got at an iteration
([CheckEv]), and the reading each operation returns. Every test of the
algorithms is a boolean (see LOGIC.md), so nothing else is left to choose.

This file has no counterpart in the Lean mechanization, which has only the
relations. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Completion.
From PC2.Appendix Require Import Control.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

(** Algorithm 2 at an iteration: the running check, if any, has not finished
([Busy]), or it has ([Done ok]), with [ok = false] if the checker failed or
gave up. *)
Inductive CheckEv := Busy | Done (ok : bool).

Section Program.

Variables (S : Type) (K : Contract S) (P : Type) (ch : Checker P) (πK : P).

Local Abbreviation Vars := (Vars K P).
Local Abbreviation Input := (Input K P).
Local Abbreviation Op := (Op K P).

(** Algorithm 2: what the verdict becomes at an iteration. A finished check
accepts only if what [check] computes holds. *)
Definition complete (ev : CheckEv) (x : Vars) : Vars :=
  match ev, req x, verdict x with
  | Done ok, Some q, Computing kl k =>
      setVerdict x
        (if ok && checkOK K ch q kl k (views x) then Correct else Incorrect)
  | _, _, _ => x
  end.

(** [complete] implements [Complete]. *)
Lemma completeP (x x₂ : Vars) :
  Complete K ch x x₂ <-> exists ev, complete ev x = x₂.
Proof.
split=> [[y|y q kl k hq hr hok|y q kl k hq hr]|[[|ok] <-]].
- by exists Busy.
- by exists (Done true); rewrite /complete hq hr hok.
- by exists (Done false); rewrite /complete hq hr.
- exact: wait.
rewrite /complete; case hq: (req x) => [q|]; last exact: wait.
case hr: (verdict x) => [|kl k||]; try exact: wait.
case: ifP => [/andP[_ hok]|_]; first exact: accept _ _ _ _ hq hr hok.
exact: reject _ _ _ _ hq hr.
Qed.

(** **Algorithm 1, one iteration**: from the variables [x], with the agent's
input [inp] and Algorithm 2's progress [ev], the operation the Airlock invokes,
and the variables once it returns with a reading. [None]: the algorithm stops,
because the certificate is rejected or the contract is not active. *)
Definition step (x : Vars) (inp : Input) (ev : CheckEv) :
    option (Op * (S -> Vars)) :=
  match phase x with
  | Init =>
      if Checker.accepts ch πK (Cert K) && stop K (record x) then
        Some (OpCtrl, fun s =>
          MkVars s (views x) (kcur x) (klast x) (req x) (verdict x) Top)
      else None
  | Top =>
      if Active K (record x) then
        let x₂ := complete ev (receive inp (publish x)) in
        if authorized x₂ then
          if req x₂ is Some q then
            Some (OpCall q, fun s =>
              MkVars s (views x₂) (kcur x₂) (Some (kcur x₂)) (req x₂) VNone
                AfterCall)
          else None
        else
          Some (OpCtrl, fun s =>
            MkVars s (views x₂) (kcur x₂).+1 (klast x₂) (req x₂) (verdict x₂)
              (phase x₂))
      else None
  | AfterCall =>
      if Active K (record x) then
        Some (OpCtrl, fun s =>
          MkVars s (views x) (kcur x).+1 (klast x) (req x) (verdict x) Top)
      else None
  end.

(** Every iteration of the program is one of the algorithm. *)
Lemma step_sound {x : Vars} {inp : Input} {ev : CheckEv} {o : Op}
    {κ : S -> Vars} :
  step x inp ev = Some (o, κ) -> Next K ch πK x inp o κ.
Proof.
rewrite /step; case hx: (phase x).
- by case: ifP => // /andP[hacc hstop] [<- <-]; exact: next_init.
- case: ifP => // ha; set x₂ := complete ev _.
  have hc : Complete K ch (receive inp (publish x)) x₂.
    by apply/completeP; exists ev.
  case: ifP => hauth; last first.
    by case=> <- <-; exact: next_ctrl _ _ _ hx ha hc (negbT hauth).
  case hq: (req x₂) => [q|//] [<- <-].
  have [hr hk] : verdict x₂ = Correct /\ kcur x₂ <= k₀ q + allow q.
    by move: hauth; rewrite /authorized hq; case: (verdict x₂).
  (* the case on [req x₂] also rewrote it in the continuation: undo it *)
  rewrite -hq; exact: next_call _ _ _ _ hx ha hc hq hr hk.
- by case: ifP => // ha [<- <-]; exact: next_ctrlAfterCall.
Qed.

(** Every iteration of the algorithm is one of the program, for some progress of
Algorithm 2. *)
Lemma step_complete {x : Vars} {inp : Input} {o : Op} {κ : S -> Vars} :
  Next K ch πK x inp o κ -> exists ev, step x inp ev = Some (o, κ).
Proof.
case=> {}x.
- by move=> {}inp hx hacc hstop; exists Busy; rewrite /step hx hacc hstop.
- move=> x₂ {}inp q hx ha /completeP[ev <-] hq hr hk; exists ev.
  by rewrite /step hx ha /= /authorized hq hr hk.
- move=> x₂ {}inp hx ha /completeP[ev <-] hauth; exists ev.
  by rewrite /step hx ha /= (negbTE hauth).
- by move=> {}inp hx ha; exists Busy; rewrite /step hx ha.
Qed.

(** **The program implements Algorithm 1.** *)
Theorem nextP (x : Vars) (inp : Input) (o : Op) (κ : S -> Vars) :
  Next K ch πK x inp o κ <-> exists ev, step x inp ev = Some (o, κ).
Proof.
by split=> [/step_complete //|[ev /step_sound //]].
Qed.

(** One iteration of a run: the input of the iteration, Algorithm 2's progress,
and the reading the operation returns with. *)
Definition advance (st : option (Vars * seq (Input * Op * S)))
    (e : Input * CheckEv * S) : option (Vars * seq (Input * Op * S)) :=
  if st is Some (x, tr) then
    if step x e.1.1 e.1.2 is Some (o, κ) then
      Some (κ e.2, rcons tr (e.1.1, o, e.2))
    else None
  else None.

(** **A run of the program**, from the reading [s₀]: the variables at the end,
and the trace, each operation with the input of its iteration and its reading.
[None]: the algorithm stopped before the end of the events. *)
Definition run (s₀ : S) (evs : seq (Input * CheckEv * S)) :
    option (Vars * seq (Input * Op * S)) :=
  foldl advance (Some (start K s₀, [::])) evs.

Lemma run_rcons (s₀ : S) (evs : seq (Input * CheckEv * S))
    (e : Input * CheckEv * S) :
  run s₀ (rcons evs e) = advance (run s₀ evs) e.
Proof. exact: foldl_rcons. Qed.

(** Every run of the program is one of the algorithm. *)
Theorem run_sound (s₀ : S) (evs : seq (Input * CheckEv * S)) (x : Vars)
    (tr : seq (Input * Op * S)) :
  run s₀ evs = Some (x, tr) -> Run K ch πK s₀ x tr.
Proof.
elim/last_ind: evs x tr => [|evs [[inp ev] s] ih] x tr.
  by case=> <- <-; exact: run_start.
rewrite run_rcons /advance; case: (run s₀ evs) ih => [[y tr'] ih|//] /=.
case hs: (step y inp ev) => [[o κ]|//] [<- <-].
exact: run_step _ (ih _ _ (erefl _)) (step_sound hs).
Qed.

(** Every run of the algorithm is one of the program, for some progress of
Algorithm 2, with the same inputs and readings. *)
Theorem run_complete (s₀ : S) (x : Vars) (tr : seq (Input * Op * S)) :
  Run K ch πK s₀ x tr ->
  exists2 evs, run s₀ evs = Some (x, tr) &
    [seq (e.1.1, e.2) | e <- evs] = [seq (t.1.1, t.2) | t <- tr].
Proof.
elim=> [|y inp o κ tr' s _ [evs hrun hmap] /step_complete[ev hs]].
  by exists [::].
exists (rcons evs (inp, ev, s)); last by rewrite !map_rcons hmap.
by rewrite run_rcons hrun /advance /= hs.
Qed.

(** The configurations the algorithm reaches are those the program reaches. *)
Corollary reach_run (s₀ : S) (x : Vars) :
  Reach K ch πK s₀ x <->
    exists evs tr, run s₀ evs = Some (x, tr).
Proof.
split=> [|[evs [tr /run_sound /run_reach //]]].
elim=> [|y inp o κ s _ [evs [tr hrun]] /step_complete[ev hs]].
  by exists [::], [::].
exists (rcons evs (inp, ev, s)), (rcons tr (inp, o, s)).
by rewrite run_rcons hrun /advance /= hs.
Qed.

(** ** The results of [Airlock] for the program *)

(** **The call discipline of A4 (iii)**, for every call the program makes from
a configuration it reaches. *)
Corollary step_call_discipline {s₀ : S} {x : Vars} {inp : Input}
    {ev : CheckEv} {q : Request K P} {κ : S -> Vars} :
  Reach K ch πK s₀ x -> step x inp ev = Some (OpCall q, κ) ->
  [/\ phase x = Top, Active K (record x) &
      checkOK K ch q (klast x) (kcur x) (views (publish x))].
Proof. by move=> hR /step_sound; exact: call_discipline hR. Qed.

(** **No veto**, for the program: whatever Algorithm 2 does, once the current
request's proof is accepted and its window is valid, with no new request, the
next operation is that call. *)
Corollary step_no_veto {x : Vars} {ev : CheckEv} {q : Request K P} {o : Op}
    {κ : S -> Vars} :
  phase x = Top -> verdict x = Correct -> req x = Some q ->
  kcur x <= k₀ q + allow q -> step x NoInput ev = Some (o, κ) -> o = OpCall q.
Proof. by move=> hx hr hq hk /step_sound; exact: no_veto. Qed.

End Program.

Arguments complete {S K P} ch ev x.
Arguments completeP {S K P} ch x x₂.
Arguments step {S} K {P} ch πK x inp ev.
Arguments step_sound {S K P ch πK x inp ev o κ} _.
Arguments step_complete {S K P ch πK x inp o κ} _.
Arguments nextP {S K P} ch πK x inp o κ.
Arguments advance {S} K {P} ch πK st e.
Arguments run {S} K {P} ch πK s₀ evs.
Arguments run_rcons {S} K {P} ch πK s₀ evs e.
Arguments run_sound {S K P ch πK s₀ evs x tr} _.
Arguments run_complete {S K P ch πK s₀ x tr} _.
Arguments reach_run {S} K {P} ch πK s₀ x.
Arguments step_call_discipline {S K P ch πK s₀ x inp ev q κ} _ _.
Arguments step_no_veto {S K P ch πK x ev q o κ} _ _ _ _ _.

(** ** The program computes

The compute-budget contract, from a pending state that may start, with a checker
that accepts the certificate (this checker is not sound in general; it only lets
the run start). Control initializes, then runs: no request is made, so every
operation is a control step, and each reading is the one given. *)
Example run_compute_budget :
  let K := ComputeBudget.contract 100 10 in
  let ch := Checker.Build (fun (_ : unit) _ => true) in
  let s₀ := ComputeBudget.MkSt 0 0 0 0 Pending in
  let s₁ := ComputeBudget.MkSt 0 0 0 1 Ongoing in
  let s₂ := ComputeBudget.MkSt 0 0 0 2 Ongoing in
  omap (fun r => [seq t.1.2 | t <- r.2])
    (run K ch tt s₀ [:: (NoInput, Busy, s₁); (NoInput, Busy, s₂)]) =
  Some [:: OpCtrl; OpCtrl].
Proof. by []. Qed.
