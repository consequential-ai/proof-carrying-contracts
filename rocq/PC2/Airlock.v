(** * The Airlock (§3.4): Algorithms 1 and 2

Algorithm 1 and the proof-checking routine of Algorithm 2 (App. B), as a
transition system at the level of operations. A configuration holds Algorithm
1's variables, Algorithm 2's shared verdict and where the loop is. From a
configuration, the steps of the loop that perform no operation (publishing the
view, receiving a request, a running check finishing or not) lead to one
operation, a tool call or a control step; when it returns, its reading becomes
the record.

The agent's requests are inputs, and when a running check finishes is left open:
the runs cover every sequence of requests and proofs, and every interleaving of
the parallel checker with the loop.

Two facts need nothing but the algorithm: every call it makes satisfies the call
discipline of A4 (iii) ([call_discipline]), and nobody can veto a call whose
proof was accepted ([no_veto]). *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Contract.

Module Checker.

(** The checker, abstractly: which proofs it accepts for which statements. A
checker is an algorithm: acceptance is a test. *)
Record t (P : Type) := Build { accepts : P -> Prop -> bool }.

(** **A1 (Sound checking).** If the checker accepts [π] as a proof of [Φ], then
[Φ] holds. *)
Definition Sound (P : Type) (ch : t P) : Prop :=
  forall (π : P) (Φ : Prop), accepts ch π Φ -> Φ.

End Checker.

Abbreviation Checker := Checker.t.

(** Algorithm 2's shared verdict [r]. A running check keeps the arguments it was
started with: the iteration of the last call, and the index of the last
published view. The iteration of the last call is [None] before the first call
(the paper's [-1]). *)
Inductive Verdict :=
  | VNone
  | Computing (kLast : option nat) (k : nat)
  | Correct
  | Incorrect.

(** Where the loop is: before initialization, at the start of an iteration, or
after a call. *)
Inductive Phase := Init | Top | AfterCall.

Definition phase_eqb (a b : Phase) : bool :=
  match a, b with Init, Init | Top, Top | AfterCall, AfterCall => true
  | _, _ => false end.

Lemma phase_eqP : Equality.axiom phase_eqb.
Proof. by case=> -[]; constructor. Qed.

HB.instance Definition _ := hasDecEq.Build Phase phase_eqP.

(** [kLast < j], for the iteration [kLast] of the last call, [None] (that is,
[-1]) before the first call. *)
Definition ltl (kLast : option nat) (j : nat) : bool :=
  if kLast is Some k then k < j else true.

Section Algorithm.

Variables (S : Type) (K : Contract S) (P : Type).

(** A request [(T, i, k₀, n, π)]: the call (a tool of the contract and an input
of it, so that [T ∈ 𝒯] and [i ∈ I_T] hold by typing), the index of the view its
proof is based on, the allowance [n], the proof. *)
Record Request := MkRequest {
  call : Call K;
  k₀ : nat;
  allow : nat;
  π : P;
}.

(** What the agent's channel gives the loop at line 6: nothing
([tool_call_ready()] is false), a request that is not of the contract's form (a
tool not in [𝒯], or an input not in [I_T]), or a request. *)
Inductive Input := NoInput | Malformed | Req (q : Request).

(** An operation of the Airlock: a control step, or the call of a request. *)
Inductive Op := OpCtrl | OpCall (q : Request).

(** The model of an operation. *)
Definition model (o : Op) : S -> S -> Prop :=
  match o with OpCtrl => ctrl K | OpCall q => D K (call q) end.

(** Algorithm 1's variables: the record (the last reading), the published views,
the number [kcur] of control steps of the loop (the paper's [k]), the iteration
[klast] of the last call, the current request; Algorithm 2's verdict; and where
the loop is. *)
Record Vars := MkVars {
  record : S;
  views : seq (V K);
  kcur : nat;
  klast : option nat;
  req : option Request;
  verdict : Verdict;
  phase : Phase;
}.

Variables (ch : Checker P) (πK : P).

(** The variables when the Airlock starts (Algorithm 1, line 1, and Algorithm
2's [r ← none]), with the record [s₀], the reading taken when the Airlock
starts. *)
Definition start (s₀ : S) : Vars := MkVars s₀ [::] 0 None None VNone Init.

(** **Algorithm 2, [check]**: what a check computes from its arguments, the
iteration [kl] of the last call and the index [k] of the last published view.
The views [v] it reads have only grown since it started. *)
Definition checkOK (q : Request) (kl : option nat) (k : nat) (v : seq (V K)) :
  bool :=
  [&& ltl kl (k₀ q), k₀ q <= k <= k₀ q + allow q &
      if onth v (k₀ q) is Some v₀ then
        Checker.accepts ch (π q) (OblN K (allow q) (call q) v₀)
      else false].

Lemma checkOKP (q : Request) (kl : option nat) (k : nat) (v : seq (V K)) :
  reflect
    [/\ ltl kl (k₀ q), k₀ q <= k <= k₀ q + allow q &
        exists2 v₀, onth v (k₀ q) = Some v₀ &
          Checker.accepts ch (π q) (OblN K (allow q) (call q) v₀)]
    (checkOK q kl k v).
Proof.
rewrite /checkOK; case: (onth v (k₀ q)) => [v₀|];
  apply: (iffP and3P) => -[h1 h2 h3]; split=> //.
- by exists v₀.
- by case: h3 => v₁ [<-].
- by case: h3 => v₁.
Qed.

(** Line 5: [v[k] ← read_view(); publish_view(k, v[k])]. *)
Definition publish (x : Vars) : Vars :=
  MkVars (record x) (rcons (views x) (view K (record x))) (kcur x) (klast x)
    (req x) (verdict x) (phase x).

(** The variables with another verdict. *)
Definition setVerdict (x : Vars) (r : Verdict) : Vars :=
  MkVars (record x) (views x) (kcur x) (klast x) (req x) r (phase x).

(** Lines 6–8: if a request arrived, [start_proof_check] replaces the current
one, and starts its check with the current [k_last] and the views published so
far, of which the check reads the index of the last (Algorithm 2). A request not
of the contract's form is replaced too, and its check fails at [T ∈ 𝒯] or at
[type_check]; nothing else depends on it. *)
Definition receive (inp : Input) (x : Vars) : Vars :=
  match inp with
  | NoInput => x
  | Malformed =>
      MkVars (record x) (views x) (kcur x) (klast x) None Incorrect (phase x)
  | Req q => MkVars (record x) (views x) (kcur x) (klast x) (Some q)
      (Computing (klast x) (size (views x)).-1) (phase x)
  end.

(** Line 9: the current request's proof is correct and [k ≤ k₀ + n]. *)
Definition authorized (x : Vars) : bool :=
  match req x, verdict x with Some q, Correct => kcur x <= k₀ q + allow q
  | _, _ => false end.

(** Algorithm 2: a running check may finish. It accepts only if what [check]
computes holds; it may reject at any time, as a real checker may also fail or
give up. *)
Inductive Complete : Vars -> Vars -> Prop :=
  | wait (x : Vars) : Complete x x
  | accept (x : Vars) (q : Request) (kl : option nat) (k : nat) :
      req x = Some q -> verdict x = Computing kl k ->
      checkOK q kl k (views x) ->
      Complete x (setVerdict x Correct)
  | reject (x : Vars) (q : Request) (kl : option nat) (k : nat) :
      req x = Some q -> verdict x = Computing kl k ->
      Complete x (setVerdict x Incorrect).

(** **Algorithm 1**, at the level of operations. From [x], with the agent's
input [inp], the Airlock invokes [o]; once [o] returns with the reading [s], the
variables are [κ s].
- [next_init] (lines 2–3): the certificate [π_𝒦] is accepted as a proof of A3
  and the state is inactive; control initializes.
- [next_call] (lines 4–10): the contract is active; the view is published (5), a
  request may arrive and its check start (6–8), a running check may finish; the
  current request's proof is correct and [k ≤ k₀ + n] (9): its call runs, then
  [k_last ← k] and the proof is consumed (10).
- [next_ctrl] (lines 4–9, 11–12): the same, with no call authorized at line 9;
  control runs, and [k ← k + 1].
- [next_ctrlAfterCall] (lines 11–12): after a call, if the contract is still
  active, control runs, and [k ← k + 1]; the loop then returns to line 4. *)
Inductive Next : Vars -> Input -> Op -> (S -> Vars) -> Prop :=
  | next_init (x : Vars) (inp : Input) :
      phase x = Init -> Checker.accepts ch πK (Cert K) -> stop K (record x) ->
      Next x inp OpCtrl
        (fun s => MkVars s (views x) (kcur x) (klast x) (req x) (verdict x) Top)
  | next_call (x x₂ : Vars) (inp : Input) (q : Request) :
      phase x = Top -> Active K (record x) ->
      Complete (receive inp (publish x)) x₂ ->
      req x₂ = Some q -> verdict x₂ = Correct -> kcur x₂ <= k₀ q + allow q ->
      Next x inp (OpCall q)
        (fun s => MkVars s (views x₂) (kcur x₂) (Some (kcur x₂)) (req x₂)
          VNone AfterCall)
  | next_ctrl (x x₂ : Vars) (inp : Input) :
      phase x = Top -> Active K (record x) ->
      Complete (receive inp (publish x)) x₂ -> ~~ authorized x₂ ->
      Next x inp OpCtrl
        (fun s => MkVars s (views x₂) (kcur x₂).+1 (klast x₂) (req x₂)
          (verdict x₂) (phase x₂))
  | next_ctrlAfterCall (x : Vars) (inp : Input) :
      phase x = AfterCall -> Active K (record x) ->
      Next x inp OpCtrl
        (fun s => MkVars s (views x) (kcur x).+1 (klast x) (req x)
          (verdict x) Top).

(** The configurations Algorithm 1 reaches from the reading [s₀], for any inputs
and readings. *)
Inductive Reach (s₀ : S) : Vars -> Prop :=
  | reach_start : Reach s₀ (start s₀)
  | reach_step (x : Vars) (inp : Input) (o : Op) (κ : S -> Vars) (s : S) :
      Reach s₀ x -> Next x inp o κ -> Reach s₀ (κ s).

(** The runs of Algorithm 1 from the reading [s₀], with their trace: each
operation, with the input of the iteration that chose it and the reading at its
end. *)
Inductive Run (s₀ : S) : Vars -> seq (Input * Op * S) -> Prop :=
  | run_start : Run s₀ (start s₀) [::]
  | run_step (x : Vars) (inp : Input) (o : Op) (κ : S -> Vars)
    (tr : seq (Input * Op * S)) (s : S) :
      Run s₀ x tr -> Next x inp o κ -> Run s₀ (κ s) (rcons tr (inp, o, s)).

(** ** The invariant of the algorithm *)

(** Algorithm 2's verdict agrees with the variables: a running check was started
for the current request with the current [k_last]; an accepted verdict means
that the current request's check passed. *)
Record Chk (x : Vars) : Prop := {
  chk_computing : forall kl k, verdict x = Computing kl k ->
    exists2 q, req x = Some q & kl = klast x /\ k <= kcur x;
  chk_correct : verdict x = Correct -> exists q v₀,
    [/\ req x = Some q, ltl (klast x) (k₀ q), k₀ q <= kcur x,
        onth (views x) (k₀ q) = Some v₀ &
        Checker.accepts ch (π q) (OblN K (allow q) (call q) v₀)];
}.

(** The invariant of Algorithm 1 between operations. *)
Record Wf (x : Vars) : Prop := {
  wf_init : phase x = Init ->
    [/\ views x = [::], kcur x = 0 & verdict x = VNone];
  wf_top : phase x = Top -> size (views x) = kcur x;
  wf_after : phase x = AfterCall ->
    [/\ size (views x) = (kcur x).+1, klast x = Some (kcur x) &
        verdict x = VNone];
  wf_chk : Chk x;
}.

(** A check that finishes changes the verdict only. *)
Lemma complete_eq {x x₂ : Vars} :
  Complete x x₂ -> exists r, x₂ = setVerdict x r.
Proof. by case=> [[] *|*|*]; eexists. Qed.

(** A check that finishes changes a running verdict only. *)
Lemma complete_verdict {x x₂ : Vars} : Complete x x₂ ->
  verdict x₂ = verdict x \/ exists kl k, verdict x = Computing kl k.
Proof.
by case=> [|? ? kl k _ hr _|? ? kl k _ hr]; [left | right; exists kl, k ..].
Qed.

(** The variables at the call-selection step of an iteration: the view is
published, and only the request and the verdict may have changed. *)
Lemma step_eq {inp : Input} {x x₂ : Vars} :
  Complete (receive inp (publish x)) x₂ ->
  exists rq r, x₂ = MkVars (record x) (rcons (views x) (view K (record x)))
    (kcur x) (klast x) rq r (phase x).
Proof. by case/complete_eq=> r ->; case: inp; eexists; eexists. Qed.

Lemma chk_publish {x : Vars} : Chk x -> Chk (publish x).
Proof.
case=> hc hr; split=> [|/hr[q [v₀ [hq hl hk hv hacc]]]]; first exact: hc.
by exists q, v₀; split=> //; exact: onth_rcons_lt.
Qed.

(** Receiving a request after publishing, at the start of an iteration. *)
Lemma chk_receive {x : Vars} {inp : Input} : Wf x -> phase x = Top ->
  Chk (receive inp (publish x)).
Proof.
move=> hW hx; case: inp => [|//|q]; first exact: chk_publish (wf_chk hW).
split=> // kl k [<- <-]; exists q => //; split=> //.
by rewrite /= size_rcons (wf_top hW hx).
Qed.

Lemma chk_complete {x x₂ : Vars} : Chk x -> Complete x x₂ -> Chk x₂.
Proof.
move=> hC h; case: h hC => [y //|y q kl k hq hr hok hC|y q kl k _ _ _];
  last by split.
split=> // _.
have [q' hq' [hkl hk]] := chk_computing hC hr.
case/checkOKP: hok => hlast /andP[hk₀ _] [v₀ hv hacc]; rewrite hkl in hlast.
by exists q, v₀; split=> //; exact: leq_trans hk.
Qed.

(** The verdict seen at the call-selection step of an iteration. *)
Lemma chk_step {x x₂ : Vars} {inp : Input} : Wf x -> phase x = Top ->
  Complete (receive inp (publish x)) x₂ -> Chk x₂.
Proof. by move=> hW hx; apply: chk_complete; exact: chk_receive. Qed.

Lemma wf_start (s₀ : S) : Wf (start s₀).
Proof. by []. Qed.

(** Algorithm 1 keeps its invariant. *)
Lemma wf_next {x : Vars} {inp : Input} {o : Op} {κ : S -> Vars} {s : S} :
  Wf x -> Next x inp o κ -> Wf (κ s).
Proof.
move=> hW h; case: h hW => {}x.
- move=> {}inp hx _ _ hW; have [hv hk hr] := wf_init hW hx.
  split=> //=; first by move=> _; rewrite hv hk.
  by split=> [kl k|]; rewrite /= hr.
- move=> x₂ {}inp q hx _ hc _ _ _ hW; case: (step_eq hc) => rq [r ->].
  by split=> //= _; rewrite size_rcons (wf_top hW hx).
- move=> x₂ {}inp hx _ hc _ hW; have hC := chk_step hW hx hc.
  case: (step_eq hc) hC => rq [r ->] hC; rewrite /= hx.
  split=> //=; first by move=> _; rewrite size_rcons (wf_top hW hx).
  split=> /= [kl k /(chk_computing hC)[q hq [hkl hk']]|/(chk_correct hC)].
    by exists q => //; split=> //; exact: leqW.
  move=> [q [v₀ [hq hl hk' hv hacc]]].
  by exists q, v₀; split=> //; exact: leqW.
- move=> {}inp hx _ hW; have [hlen _ hr] := wf_after hW hx.
  split=> //=.
  by split=> [kl k|]; rewrite /= hr.
Qed.

Lemma reach_wf {s₀ : S} {x : Vars} : Reach s₀ x -> Wf x.
Proof.
by elim=> [|{}x inp o κ s _ ih hn]; [exact: wf_start | exact: wf_next hn].
Qed.

Lemma run_reach {s₀ : S} {x : Vars} {tr : seq (Input * Op * S)} :
  Run s₀ x tr -> Reach s₀ x.
Proof.
by elim=> [|{}x inp o κ {}tr s _ ih hn];
  [exact: reach_start | exact: reach_step hn].
Qed.

(** ** A4 (iii), and no veto *)

(** The facts behind a call, from Algorithm 1's invariant (A4 (iii)). *)
Lemma call_facts {x : Vars} {inp : Input} {q : Request} {κ : S -> Vars} :
  Wf x -> Next x inp (OpCall q) κ ->
  [/\ phase x = Top, Active K (record x) &
      checkOK q (klast x) (kcur x) (views (publish x))].
Proof.
move=> hW h; move eo: (OpCall q) h => o h.
case: h eo hW => // {}x x₂ {}inp q' hx ha hc hq hr hk [->] hW.
have := chk_correct (chk_step hW hx hc) hr.
case: (step_eq hc) hq hk => rq [r ->] /= -> hk
  [_ [v₀ [[<-] hlast hk₀ hv hacc]]].
by split=> //; apply/checkOKP; split=> //; [rewrite hk₀ | exists v₀].
Qed.

(** **The call discipline of A4 (iii) follows from Algorithms 1 and 2.** A call
runs only from an active state at the start of an iteration [k], for the current
request [(T, i, k₀, n, π)], if no other call ran since [v[k₀]] was published
([kLast < k₀]), with [k₀ ≤ k ≤ k₀ + n], after the checker accepted [π] as a
proof of [Obl^{≤n}_T(i, v[k₀])], a statement the Airlock forms itself from the
published view [v[k₀]]. *)
Theorem call_discipline {s₀ : S} {x : Vars} {inp : Input} {q : Request}
    {κ : S -> Vars} :
  Reach s₀ x -> Next x inp (OpCall q) κ ->
  [/\ phase x = Top, Active K (record x) &
      checkOK q (klast x) (kcur x) (views (publish x))].
Proof. by move=> /reach_wf; exact: call_facts. Qed.

(** **No veto (§4.2).** If the current request's proof has been accepted and its
window is still valid, and the agent sends no new request, the next operation is
that call: nothing else can intervene. *)
Theorem no_veto {x : Vars} {q : Request} {o : Op} {κ : S -> Vars} :
  phase x = Top -> verdict x = Correct -> req x = Some q ->
  kcur x <= k₀ q + allow q -> Next x NoInput o κ -> o = OpCall q.
Proof.
move=> hx hr hq hk h; move ei: NoInput h => inp h.
case: h ei hx hr hq hk => {}x.
- by move=> {}inp hI _ _ _ hx; rewrite hI in hx.
- move=> x₂ {}inp q' _ _ hc hq' _ _ ei _ _ hq _; subst inp.
  by case: (complete_eq hc) hq' => r -> /=; rewrite hq => -[->].
- move=> x₂ {}inp _ _ hc /negP hno ei _ hr hq hk;
  subst inp; exfalso; apply: hno.
  case: (complete_eq hc) (complete_verdict hc) => r -> /=;
    rewrite hr => -[->|[kl [k' //]]].
  by rewrite /authorized /= hq.
- by move=> {}inp hA _ _ hx; rewrite hA in hx.
Qed.

End Algorithm.

Arguments start {S} K {P} s₀.
Arguments model {S K P} o _ _.
Arguments publish {S K P} x.
Arguments setVerdict {S K P} x r.
Arguments receive {S K P} inp x.
Arguments checkOK {S} K {P} ch q kl k v.
Arguments checkOKP {S} K {P} ch q kl k v.
Arguments Complete {S} K {P} ch _ _.
Arguments Next {S} K {P} ch πK _ _ _ _.
Arguments Reach {S} K {P} ch πK s₀ _.
Arguments Run {S} K {P} ch πK s₀ _ _.
Arguments Chk {S} K {P} ch x.
Arguments Wf {S} K {P} ch x.
Arguments NoInput {S K P}.
Arguments Malformed {S K P}.
Arguments Req {S K P} q.
Arguments OpCtrl {S K P}.
Arguments OpCall {S K P} q.
Arguments wait {S K P ch} x.
Arguments accept {S K P ch} x q kl k _ _ _.
Arguments reject {S K P ch} x q kl k _ _.
Arguments next_init {S K P ch πK} x inp _ _ _.
Arguments next_call {S K P ch πK} x x₂ inp q _ _ _ _ _ _.
Arguments next_ctrl {S K P ch πK} x x₂ inp _ _ _ _.
Arguments next_ctrlAfterCall {S K P ch πK} x inp _ _.
Arguments reach_start {S K P ch πK s₀}.
Arguments reach_step {S K P ch πK s₀ x inp o κ} s _ _.
Arguments run_start {S K P ch πK s₀}.
Arguments run_step {S K P ch πK s₀ x inp o κ tr} s _ _.
Arguments authorized {S K P} x.
Arguments complete_eq {S K P ch x x₂} _.
Arguments complete_verdict {S K P ch x x₂} _.
Arguments step_eq {S K P ch inp x x₂} _.
Arguments chk_publish {S K P ch x} _.
Arguments chk_receive {S K P ch x inp} _ _.
Arguments chk_complete {S K P ch x x₂} _ _.
Arguments chk_step {S K P ch x x₂ inp} _ _ _.
Arguments wf_start {S K P ch} s₀.
Arguments wf_next {S K P ch πK x inp o κ s} _ _.
Arguments reach_wf {S K P ch πK s₀ x} _.
Arguments run_reach {S K P ch πK s₀ x tr} _.
Arguments call_facts {S K P ch πK x inp q κ} _ _.
Arguments call_discipline {S K P ch πK s₀ x inp q κ} _ _.
Arguments no_veto {S K P ch πK x q o κ} _ _ _ _ _.
