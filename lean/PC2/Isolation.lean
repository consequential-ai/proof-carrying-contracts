import PC2.World

/-!
# Isolation (§5.2, App. G): Lemma G.1 and Lemma 2

An invocation of a routine runs alongside the environment, the host and the agent. A configuration
holds the world, the state, and the local states of the routine, the host and the agent; each actor has
a step relation. An invocation prefix is a finite sequence of steps from the routine's initial state,
taken while the routine has not returned. A reference prefix has no step of the agent.

A7 (isolation) is stated stepwise, as in App. G: (NI1) the agent's steps leave the protected part — the
world, the state and the routine — unchanged; (NI2) what the other actors do to the protected part does
not depend on the rest. Then every invocation prefix has a reference prefix with the same protected
endpoint (Lemma G.1), so the effects with any agent are among the reference effects (Lemma 2), and
coverage and fidelity established for reference executions hold for every agent.
-/

namespace PC2

/-- **Definition G.1**: a configuration, the world, the state, and the local states of the routine,
the host and the agent. -/
structure Conf (W S R U A : Type) where
  w : W
  s : S
  r : R
  u : U
  a : A

/-- The actors. -/
inductive Actor where
  | routine
  | env
  | host
  | agent
  deriving DecidableEq

section

variable {W S R U A : Type}

/-- The protected part `κ_R(c) = (w, s, r)`. -/
def Conf.prot (c : Conf W S R U A) : W × S × R := (c.w, c.s, c.r)

/-- Invocation prefixes: steps of the actors, each taken while the routine has not returned. -/
inductive Prefix (step : Actor → Conf W S R U A → Conf W S R U A → Prop) (ret : R → Prop) :
    Conf W S R U A → Conf W S R U A → Prop
  | refl (c : Conf W S R U A) : Prefix step ret c c
  | snoc {c₀ c c' : Conf W S R U A} (b : Actor) :
      Prefix step ret c₀ c → ¬ ret c.r → step b c c' → Prefix step ret c₀ c'

theorem Prefix.trans {step : Actor → Conf W S R U A → Conf W S R U A → Prop} {ret : R → Prop}
    {a b c : Conf W S R U A} (h₁ : Prefix step ret a b) (h₂ : Prefix step ret b c) :
    Prefix step ret a c := by
  induction h₂ with
  | refl => exact h₁
  | snoc b _ hr hs ih => exact .snoc b ih hr hs

/-- The steps of the actors other than the agent: reference executions. -/
def refStep (step : Actor → Conf W S R U A → Conf W S R U A → Prop) :
    Actor → Conf W S R U A → Conf W S R U A → Prop :=
  fun b c c' => b ≠ .agent ∧ step b c c'

/-- **(NI1) Preservation by the agent.** -/
def NI1 (step : Actor → Conf W S R U A → Conf W S R U A → Prop) : Prop :=
  ∀ c c', step .agent c c' → c'.prot = c.prot

/-- **(NI2) Independence of the protected evolution.** -/
def NI2 (step : Actor → Conf W S R U A → Conf W S R U A → Prop) (ret : R → Prop) : Prop :=
  ∀ (b : Actor) (c c' d : Conf W S R U A), b ≠ .agent → ¬ ret c.r → step b c c' →
    d.prot = c.prot → ∃ d', Prefix (refStep step) ret d d' ∧ d'.prot = c'.prot

/-- **Lemma G.1 (Isolation, stepwise formulation).** Under (NI1) and (NI2), every invocation prefix has
a reference prefix from the same configuration that ends with the same protected part. -/
theorem isolation_stepwise {step : Actor → Conf W S R U A → Conf W S R U A → Prop}
    {ret : R → Prop} (h1 : NI1 step) (h2 : NI2 step ret) {c₀ c : Conf W S R U A}
    (h : Prefix step ret c₀ c) : ∃ d, Prefix (refStep step) ret c₀ d ∧ d.prot = c.prot := by
  induction h with
  | refl => exact ⟨c₀, .refl _, rfl⟩
  | @snoc c c' b _ hr hs ih =>
    obtain ⟨d, hd, hκ⟩ := ih
    by_cases hb : b = .agent
    · subst hb
      exact ⟨d, hd, hκ.trans (h1 c c' hs).symm⟩
    · obtain ⟨d', hd', hκ'⟩ := h2 b c c' d hb hr hs hκ
      exact ⟨d', hd.trans hd', hκ'⟩

end

/-! ## The deployment, the agent, and Lemma 2 -/

variable {S : Type}

/-- **The step model of a deployment** (App. G): the local states of routines, host and agent; the
initial states of the routine of each call and of control (`none`); when a routine has returned; and
the steps of the routine, the environment and the host. -/
structure System (K : Contract S) (W : Type) where
  R : Type
  U : Type
  A : Type
  start : Option K.Call → R → Prop
  ret : R → Prop
  routine : Conf W S R U A → Conf W S R U A → Prop
  env : Conf W S R U A → Conf W S R U A → Prop
  host : Conf W S R U A → Conf W S R U A → Prop

namespace System

variable {K : Contract S} {W : Type} (sys : System K W)

/-- An agent: the steps of every process that runs for it. -/
abbrev Agent := Conf W S sys.R sys.U sys.A → Conf W S sys.R sys.U sys.A → Prop

/-- The steps of the actors, with the agent `α`. -/
def step (α : sys.Agent) : Actor → Conf W S sys.R sys.U sys.A → Conf W S sys.R sys.U sys.A → Prop
  | .routine => sys.routine
  | .env => sys.env
  | .host => sys.host
  | .agent => α

/-- Without the agent: the steps of reference executions. -/
def noAgent : sys.Agent := fun _ _ => False

/-- `Ê^α`: an invocation prefix of the routine of `o` (a call, or control for `none`), with the agent
`α`, from the world `w` and the state `s`, reaches `(w', s')`. -/
def reach (α : sys.Agent) (o : Option K.Call) (w : W) (s : S) (w' : W) (s' : S) : Prop :=
  ∃ c₀ c : Conf W S sys.R sys.U sys.A, sys.start o c₀.r ∧ c₀.w = w ∧ c₀.s = s ∧
    Prefix (sys.step α) sys.ret c₀ c ∧ c.w = w' ∧ c.s = s'

/-- `Ê^•`: the same, in reference executions, with no step of the agent. -/
def refReach (o : Option K.Call) (w : W) (s : S) (w' : W) (s' : S) : Prop :=
  ∃ c₀ c : Conf W S sys.R sys.U sys.A, sys.start o c₀.r ∧ c₀.w = w ∧ c₀.s = s ∧
    Prefix (refStep (sys.step sys.noAgent)) sys.ret c₀ c ∧ c.w = w' ∧ c.s = s'

/-- The effects of the deployment with the agent `α`. -/
def effects (α : sys.Agent) : Effects K W := ⟨fun c => sys.reach α (some c), sys.reach α none⟩

/-- The effects of reference executions. -/
def refEffects : Effects K W := ⟨fun c => sys.refReach (some c), sys.refReach none⟩

/-- **A7 (Isolation)**, stepwise: (NI1) for the agent, (NI2) for the other actors. NI2 does not mention
the agent. -/
structure Isolation (α : sys.Agent) : Prop where
  ni1 : NI1 (sys.step α)
  ni2 : NI2 (sys.step sys.noAgent) sys.ret

/-- **A7 (Isolation of the agent)**, in the form stated in §5.2.
- (i) Nothing the agent does changes the world, the state, or the internal state of a running routine.
- (ii) Each routine receives from the agent only the call input, fixed at invocation. In this model the
  routine's initial state is given by the call alone (`start`), so (ii) holds by construction.
- (iii) How the world, the state and the routine's internal state evolve during an invocation depends
  only on their current values (the routine's state contains its fixed input): a change that another
  actor makes to them from one configuration, it can make from any configuration that agrees with it on
  them, whatever the host and the agent are doing. -/
structure A7 (α : sys.Agent) : Prop where
  i : ∀ c c', α c c' → c'.prot = c.prot
  iii : ∀ (b : Actor) (c c' d : Conf W S sys.R sys.U sys.A), b ≠ .agent → ¬ sys.ret c.r →
    sys.step α b c c' → d.prot = c.prot →
    c'.prot = c.prot ∨ ∃ d', sys.step α b d d' ∧ d'.prot = c'.prot

theorem step_ne_agent (α β : sys.Agent) {b : Actor} (hb : b ≠ .agent) : sys.step α b = sys.step β b := by
  cases b with
  | agent => exact absurd rfl hb
  | _ => rfl

/-- **The stated isolation is sufficient for the stepwise one** (App. G): A7 (i) is (NI1), and A7 (iii)
gives (NI2), the matching sequence having at most one step. -/
theorem A7.isolation {α : sys.Agent} (h : sys.A7 α) : sys.Isolation α where
  ni1 := h.i
  ni2 b c c' d hb hr hs hκ := by
    have hs' : sys.step α b c c' := by rw [sys.step_ne_agent α sys.noAgent hb]; exact hs
    rcases h.iii b c c' d hb hr hs' hκ with heq | ⟨d', hd, hκ'⟩
    · exact ⟨d, .refl d, hκ.trans heq.symm⟩
    · have hrd : ¬ sys.ret d.r := by
        have : d.r = c.r := congrArg (fun p => p.2.2) hκ
        rw [this]; exact hr
      refine ⟨d', .snoc b (.refl d) hrd ⟨hb, ?_⟩, hκ'⟩
      rw [sys.step_ne_agent sys.noAgent α hb]; exact hd

theorem refStep_agent (α β : sys.Agent) : refStep (sys.step α) = refStep (sys.step β) := by
  funext b c c'
  cases b <;> simp [refStep, step]

/-- **Lemma 2 (Isolation).** Under A7, for every agent, every effect of an invocation is an effect of a
reference execution. -/
theorem isolation (α : sys.Agent) (hA7 : sys.Isolation α) (o : Option K.Call) (w : W) (s : S)
    (w' : W) (s' : S) (h : sys.reach α o w s w' s') : sys.refReach o w s w' s' := by
  obtain ⟨c₀, c, hst, hw, hs, hp, hw', hs'⟩ := h
  have hni2 : NI2 (sys.step α) sys.ret := by
    intro b c c' d hb hr hstep hκ
    have hstep' : sys.step sys.noAgent b c c' := by cases b <;> first | exact absurd rfl hb | exact hstep
    obtain ⟨d', hd', hκ'⟩ := hA7.ni2 b c c' d hb hr hstep' hκ
    exact ⟨d', by rw [sys.refStep_agent α sys.noAgent]; exact hd', hκ'⟩
  obtain ⟨d, hd, hκ⟩ := isolation_stepwise hA7.ni1 hni2 hp
  have hwd : d.w = c.w := congrArg Prod.fst hκ
  have hsd : d.s = c.s := congrArg (fun p => p.2.1) hκ
  refine ⟨c₀, d, hst, hw, hs, ?_, hwd.trans hw', hsd.trans hs'⟩
  rw [sys.refStep_agent sys.noAgent α]; exact hd

/-- Coverage established for reference executions holds for every agent (via Lemma 2). -/
theorem coverage_of_ref (α : sys.Agent) (hA7 : sys.Isolation α) (h : Coverage K sys.refEffects) :
    Coverage K (sys.effects α) where
  call c s s' hen := fun ⟨w, w', he⟩ =>
    h.call c s s' hen ⟨w, w', sys.isolation α hA7 (some c) w s w' s' he⟩
  ctrl s s' hen := fun ⟨w, w', he⟩ =>
    h.ctrl s s' hen ⟨w, w', sys.isolation α hA7 none w s w' s' he⟩

/-- Fidelity established for reference executions holds for every agent (via Lemma 2). -/
theorem fidelity_of_ref (α : sys.Agent) (hA7 : sys.Isolation α) {ρ : W → S → Prop}
    (h : Fidelity K sys.refEffects ρ) : Fidelity K (sys.effects α) ρ where
  call c w s w' s' hρ hen he := h.call c w s w' s' hρ hen (sys.isolation α hA7 (some c) w s w' s' he)
  ctrl w s w' s' hρ hen he := h.ctrl w s w' s' hρ hen (sys.isolation α hA7 none w s w' s' he)
  init w s w' s' hin ha he := h.init w s w' s' hin ha (sys.isolation α hA7 none w s w' s' he)

end System

end PC2

namespace PC2

variable {S : Type}

/-- **Appendix F: what goes wrong without isolation.** If, while an operation admissible at a compliant
state `s` that describes the world `w` runs, something outside the proof gate makes the world unsafe,
then coverage, fidelity and adequacy cannot all hold. -/
theorem ungated_unsafe {K : Contract S} {W P : Type} {E : Effects K W} {ρ : W → S → Prop}
    {Safe : W → Prop} {o : Op K P} {w w' : W} {s s' : S} (hρ : ρ w s) (hadm : wp o.model K.C s)
    (he : E.op o w s w' s') (hunsafe : ¬ Safe w') :
    ¬ (Coverage K E ∧ Fidelity K E ρ ∧ Adequacy K ρ Safe) := by
  intro ⟨hA2, hA5, hA6⟩
  exact hunsafe (hA6 w' s' (hA5.op hρ hadm.1 he) (hadm.2 s' (hA2.op hadm.1 he)))

end PC2
