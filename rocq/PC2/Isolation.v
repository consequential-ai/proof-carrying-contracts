(** * Isolation (§5.2, App. G): Lemma G.1 and Lemma 2

An invocation of a routine runs alongside the environment, the host and the
agent. A configuration holds the world, the state, and the local states of the
routine, the host and the agent; each actor has a step relation. An invocation
prefix is a finite sequence of steps from the routine's initial state, taken
while the routine has not returned. A reference prefix has no step of the agent.

A7 (isolation) is stated stepwise, as in App. G: (NI1) the agent's steps leave
the protected part — the world, the state and the routine — unchanged; (NI2)
what the other actors do to the protected part does not depend on the rest. Then
every invocation prefix has a reference prefix with the same protected endpoint
(Lemma G.1), so the effects with any agent are among the reference effects
(Lemma 2), and coverage and fidelity established for reference executions hold
for every agent. *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From PC2 Require Import Basic Airlock Execution World.

Unset Printing Implicit Defensive.

Import Contract.

Module Conf.

(** **Definition G.1**: a configuration, the world, the state, and the local
states of the routine, the host and the agent. *)
Record t (W S R U A : Type) := Build { w : W; s : S; r : R; u : U; a : A }.

Arguments Build {W S R U A} w s r u a.
Arguments w {W S R U A} t.
Arguments s {W S R U A} t.
Arguments r {W S R U A} t.
Arguments u {W S R U A} t.
Arguments a {W S R U A} t.

(** The protected part [κ_R(c) = (w, s, r)]. *)
Definition prot {W S R U A : Type} (c : t W S R U A) : W * S * R :=
  (w c, s c, r c).

End Conf.

Abbreviation Conf := Conf.t.

Module Actor.

(** The actors. *)
Inductive t := routine | env | host | agent.

End Actor.

Section Prefix.

Context {W S R U A : Type}.

(** Invocation prefixes: steps of the actors, each taken while the routine has
not returned. *)
Inductive Prefix (step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop)
    (ret : R -> Prop) : Conf W S R U A -> Conf W S R U A -> Prop :=
  | prefix_refl (c : Conf W S R U A) : Prefix step ret c c
  | prefix_snoc (c₀ c c' : Conf W S R U A) (b : Actor.t) :
      Prefix step ret c₀ c -> ~ ret (Conf.r c) -> step b c c' ->
      Prefix step ret c₀ c'.

Arguments prefix_refl {step ret} c.
Arguments prefix_snoc {step ret c₀ c c'} b _ _ _.

Lemma prefix_trans {step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop}
    {ret : R -> Prop} {a b c : Conf W S R U A} :
  Prefix step ret a b -> Prefix step ret b c -> Prefix step ret a c.
Proof.
move=> h₁ h₂; elim: h₂ h₁ => // c₀ {}c c' b' _ ih hr hs h₁.
exact: prefix_snoc b' (ih h₁) hr hs.
Qed.

(** Prefixes for fewer steps are prefixes for more. *)
Lemma prefix_mono
    {step step' : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop}
    {ret : R -> Prop} {c₀ c : Conf W S R U A} :
  (forall b c c', step b c c' -> step' b c c') ->
  Prefix step ret c₀ c -> Prefix step' ret c₀ c.
Proof.
move=> h; elim=> [{}c|{}c₀ {}c c' b _ ih hr hs]; first exact: prefix_refl.
exact: prefix_snoc b ih hr (h _ _ _ hs).
Qed.

(** The steps of the actors other than the agent: reference executions. *)
Definition refStep
    (step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop) :
  Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop :=
  fun b c c' => b <> Actor.agent /\ step b c c'.

(** **(NI1) Preservation by the agent.** *)
Definition NI1
    (step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop) : Prop :=
  forall c c', step Actor.agent c c' -> Conf.prot c' = Conf.prot c.

(** **(NI2) Independence of the protected evolution.** *)
Definition NI2
    (step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop)
    (ret : R -> Prop) : Prop :=
  forall (b : Actor.t) (c c' d : Conf W S R U A), b <> Actor.agent ->
    ~ ret (Conf.r c) -> step b c c' -> Conf.prot d = Conf.prot c ->
    exists d', Prefix (refStep step) ret d d' /\ Conf.prot d' = Conf.prot c'.

(** **Lemma G.1 (Isolation, stepwise formulation).** Under (NI1) and (NI2),
every invocation prefix has a reference prefix from the same configuration that
ends with the same protected part. *)
Theorem isolation_stepwise
    {step : Actor.t -> Conf W S R U A -> Conf W S R U A -> Prop}
    {ret : R -> Prop} (h1 : NI1 step) (h2 : NI2 step ret)
    {c₀ c : Conf W S R U A} :
  Prefix step ret c₀ c ->
  exists d, Prefix (refStep step) ret c₀ d /\ Conf.prot d = Conf.prot c.
Proof.
elim=> [{}c|{}c₀ {}c c' b _ [d [hd hκ]] hr hs];
  first by exists c; split; first exact: prefix_refl.
have key : b <> Actor.agent ->
    exists d0, Prefix (refStep step) ret c₀ d0 /\ Conf.prot d0 = Conf.prot c'.
  move=> hb; have [d' [hd' hκ']] := h2 b c c' d hb hr hs hκ.
  by exists d'; split=> //; exact: prefix_trans hd hd'.
case: b hs key => hs key; try by apply: key.
by exists d; split=> //; rewrite hκ (h1 c c' hs).
Qed.

End Prefix.

Arguments prefix_refl {W S R U A step ret} c.
Arguments prefix_snoc {W S R U A step ret c₀ c c'} b _ _ _.

(** ** The deployment, the agent, and Lemma 2 *)

Module System.

(** **The step model of a deployment** (App. G): the local states of routines,
host and agent; the initial states of the routine of each call and of control
([None]); when a routine has returned; and the steps of the routine, the
environment and the host. *)
Record t {S : Type} (K : Contract S) (W : Type) := Build {
  R : Type;
  U : Type;
  A : Type;
  start : option (Call K) -> R -> Prop;
  ret : R -> Prop;
  routine : Conf W S R U A -> Conf W S R U A -> Prop;
  env : Conf W S R U A -> Conf W S R U A -> Prop;
  host : Conf W S R U A -> Conf W S R U A -> Prop;
}.

Arguments R {S K W} t.
Arguments U {S K W} t.
Arguments A {S K W} t.
Arguments start {S K W} t _ _.
Arguments ret {S K W} t _.
Arguments routine {S K W} t _ _.
Arguments env {S K W} t _ _.
Arguments host {S K W} t _ _.

Section System.

Context {S : Type} {K : Contract S} {W : Type} (sys : t K W).

Abbreviation Cf := (Conf W S (R sys) (U sys) (A sys)).

(** An agent: the steps of every process that runs for it. *)
Definition Agent := Cf -> Cf -> Prop.

(** The steps of the actors, with the agent [α]. *)
Definition step (α : Agent) (b : Actor.t) : Cf -> Cf -> Prop :=
  match b with
  | Actor.routine => routine sys
  | Actor.env => env sys
  | Actor.host => host sys
  | Actor.agent => α
  end.

(** Without the agent: the steps of reference executions. *)
Definition noAgent : Agent := fun _ _ => False.

(** An invocation prefix of the routine of [o] (a call, or control for [None]),
for the steps [st], from the world [w] and the state [s], reaches [(w', s')]. *)
Definition reachBy (st : Actor.t -> Cf -> Cf -> Prop) (o : option (Call K))
    (w : W) (s : S) (w' : W) (s' : S) : Prop :=
  exists c₀ c : Cf,
    [/\ start sys o (Conf.r c₀), (Conf.w c₀, Conf.s c₀) = (w, s),
        Prefix st (ret sys) c₀ c & (Conf.w c, Conf.s c) = (w', s')].

(** [Ê^α]: with the agent [α]. *)
Definition reach (α : Agent) : option (Call K) -> W -> S -> W -> S -> Prop :=
  reachBy (step α).

(** [Ê^•]: in reference executions, with no step of the agent. *)
Definition refReach : option (Call K) -> W -> S -> W -> S -> Prop :=
  reachBy (refStep (step noAgent)).

(** The effects of the deployment with the agent [α]. *)
Definition effects (α : Agent) : Effects K W :=
  Effects.Build (fun c => reach α (Some c)) (reach α None).

(** The effects of reference executions. *)
Definition refEffects : Effects K W :=
  Effects.Build (fun c => refReach (Some c)) (refReach None).

(** **A7 (Isolation)**, stepwise: (NI1) for the agent, (NI2) for the other
actors. NI2 does not mention the agent. *)
Record Isolation (α : Agent) : Prop := {
  ni1 : NI1 (step α);
  ni2 : NI2 (step noAgent) (ret sys);
}.

(** **A7 (Isolation of the agent)**, in the form stated in §5.2.
- (i) Nothing the agent does changes the world, the state, or the internal state
  of a running routine.
- (ii) Each routine receives from the agent only the call input, fixed at
  invocation. In this model the routine's initial state is given by the call
  alone ([start]), so (ii) holds by construction.
- (iii) How the world, the state and the routine's internal state evolve during
  an invocation depends only on their current values (the routine's state
  contains its fixed input): a change that another actor makes to them from one
  configuration, it can make from any configuration that agrees with it on them,
  whatever the host and the agent are doing. *)
Record A7 (α : Agent) : Prop := {
  a7_i : forall c c', α c c' -> Conf.prot c' = Conf.prot c;
  a7_iii : forall (b : Actor.t) (c c' d : Cf), b <> Actor.agent ->
    ~ ret sys (Conf.r c) -> step α b c c' -> Conf.prot d = Conf.prot c ->
    Conf.prot c' = Conf.prot c \/
    exists d', step α b d d' /\ Conf.prot d' = Conf.prot c';
}.

(** The actors other than the agent take the same steps whatever the agent. *)
Lemma step_ne_agent (α β : Agent) {b : Actor.t} {c c' : Cf} :
  b <> Actor.agent -> step α b c c' -> step β b c c'.
Proof. by case: b. Qed.

Lemma refStep_agent (α β : Agent) (b : Actor.t) (c c' : Cf) :
  refStep (step α) b c c' -> refStep (step β) b c c'.
Proof. by case=> hb hs; split=> //; exact: step_ne_agent hb hs. Qed.

(** **The stated isolation is sufficient for the stepwise one** (App. G): A7 (i)
is (NI1), and A7 (iii) gives (NI2), the matching sequence having at most one
step. *)
Theorem A7_isolation {α : Agent} : A7 α -> Isolation α.
Proof.
move=> h; split; first exact: a7_i _ h.
move=> b c c' d hb hr hs hκ.
have hs' := step_ne_agent noAgent α hb hs.
case: (a7_iii _ h b c c' d hb hr hs' hκ) => [heq|[d' [hd hκ']]].
  by exists d; split; [exact: prefix_refl | rewrite hκ heq].
have hrd : ~ ret sys (Conf.r d) by move: hκ => [_ _ ->].
exists d'; split=> //.
exact: (prefix_snoc b (prefix_refl d) hrd
  (conj hb (step_ne_agent α noAgent hb hd))).
Qed.

(** **Lemma 2 (Isolation).** Under A7, for every agent, every effect of an
invocation is an effect of a reference execution. *)
Theorem isolation (α : Agent) (hA7 : Isolation α) (o : option (Call K))
    (w : W) (s : S) (w' : W) (s' : S) :
  reach α o w s w' s' -> refReach o w s w' s'.
Proof.
move=> [c₀ [c [hst hws hp hws']]].
have hni2 : NI2 (step α) (ret sys).
  move=> b c1 c1' d hb hr hstep hκ.
  have [d' [hd' hκ']] := ni2 _ hA7 b c1 c1' d hb hr
    (step_ne_agent α noAgent hb hstep) hκ.
  by exists d'; split=> //; exact: prefix_mono (refStep_agent noAgent α) hd'.
have [d [hd hκ]] := isolation_stepwise (ni1 _ hA7) hni2 hp.
exists c₀, d; split=> //; first exact: prefix_mono (refStep_agent α noAgent) hd.
by case: hκ => -> -> _.
Qed.

(** Coverage established for reference executions holds for every agent (via
Lemma 2). *)
Theorem coverage_of_ref (α : Agent) (hA7 : Isolation α) :
  Coverage K refEffects -> Coverage K (effects α).
Proof.
move=> h; split=> [c s s' hen [w [w' he]]|s s' hen [w [w' he]]].
  by apply: (cov_call h) hen _; exists w, w'; exact: isolation hA7 _ _ _ _ _ he.
by apply: (cov_ctrl h) hen _; exists w, w'; exact: isolation hA7 _ _ _ _ _ he.
Qed.

(** Fidelity established for reference executions holds for every agent (via
Lemma 2). *)
Theorem fidelity_of_ref (α : Agent) (hA7 : Isolation α) {ρ : W -> S -> Prop} :
  Fidelity K refEffects ρ -> Fidelity K (effects α) ρ.
Proof.
move=> h;
  split=> [c w s w' s' hρ hen he|w s w' s' hρ hen he|w s w' s' hin ha he].
- exact: fid_call h c w s w' s' hρ hen (isolation α hA7 (Some c) w s w' s' he).
- exact: fid_ctrl h w s w' s' hρ hen (isolation α hA7 None w s w' s' he).
- exact: fid_init h w s w' s' hin ha (isolation α hA7 None w s w' s' he).
Qed.

(** Under A7 as stated in §5.2, coverage and fidelity established for reference
executions hold for every agent. *)
Corollary coverage_of_A7 (α : Agent) (hA7 : A7 α) :
  Coverage K refEffects -> Coverage K (effects α).
Proof. exact: coverage_of_ref (A7_isolation hA7). Qed.

Corollary fidelity_of_A7 (α : Agent) (hA7 : A7 α) {ρ : W -> S -> Prop} :
  Fidelity K refEffects ρ -> Fidelity K (effects α) ρ.
Proof. by move=> h; exact: (fidelity_of_ref α (A7_isolation hA7) h). Qed.

End System.

Arguments Agent {S K W} sys.
Arguments step {S K W} sys α _ _ _.
Arguments noAgent {S K W} sys _ _.
Arguments reachBy {S K W} sys st o w s w' s'.
Arguments reach {S K W} sys α _ _ _ _ _.
Arguments refReach {S K W} sys _ _ _ _ _.
Arguments effects {S K W} sys α.
Arguments refEffects {S K W} sys.
Arguments Isolation {S K W} sys α.
Arguments A7 {S K W} sys α.
Arguments A7_isolation {S K W sys α} _.
Arguments isolation {S K W} sys α hA7 o w s w' s' _.
Arguments coverage_of_ref {S K W} sys α hA7 _.
Arguments fidelity_of_ref {S K W} sys α hA7 {ρ} _.
Arguments coverage_of_A7 {S K W} sys α hA7 _.
Arguments fidelity_of_A7 {S K W} sys α hA7 {ρ} _.
Arguments a7_i {S K W sys α} _ c c' _.
Arguments a7_iii {S K W sys α} _ b c c' d _ _ _ _.
Arguments ni1 {S K W sys α} _ c c' _.
Arguments ni2 {S K W sys α} _ b c c' d _ _ _ _.

End System.

(** **Appendix F: what goes wrong without isolation.** If, while an operation
admissible at a compliant state [s] that describes the world [w] runs, something
outside the proof gate makes the world unsafe, then coverage, fidelity and
adequacy cannot all hold. *)
Theorem ungated_unsafe {S : Type} {K : Contract S} {W P : Type}
    {E : Effects K W} {ρ : W -> S -> Prop} {Safe : W -> Prop} {o : Op K P}
    {w w' : W} {s s' : S} :
  ρ w s -> wp (model o) (C K) s -> Effects.op E o w s w' s' -> ~ Safe w' ->
  ~ [/\ Coverage K E, Fidelity K E ρ & Adequacy K ρ Safe].
Proof.
move=> hρ [hen hall] he hunsafe [hA2 hA5 hA6]; apply: hunsafe.
exact: hA6 _ _ (fidelity_op hA5 hρ hen he) (hall _ (coverage_op hA2 hen he)).
Qed.
