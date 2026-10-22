import PC2.Airlock

/-!
# Executions (§4.1): effects, coverage, and A4

What happens when the Airlock invokes a routine is described by the **effects** `Ê` of the deployment:
from a world and a state, the world–state pairs an invocation can reach at any instant of its
execution, outside changes included (§5.1). Their projection on states is `E` (§4.1). Coverage (A2)
asks each model to contain the states that execution can reach where the call is enabled.

An **execution** is a run of Algorithms 1–2 in which each operation is a segment of time: the world and
the state at each of its instants. A4 is the statement that the actual execution of a deployment is one
of these: (i) every segment starts where the previous one ended, the first at the initial reading; (ii)
the reading after an operation is the state at the instant it returns; (iii) the operations are those
Algorithms 1–2 choose. That every instant from the start belongs to some operation is also A4 (i);
App. D shows how to make it true when the host takes time between routines.

Instants are abstract: a segment has its own type of instants (an interval of real time, ticks,
anything), and no property of time is used.
-/

namespace PC2

variable {S : Type}

/-- The effects `Ê` of a deployment: `call c w s w' s'` holds when an invocation of the call `c`
starting in the world `w` and the state `s` can reach `(w', s')` at some instant of its execution;
`ctrl` likewise for the control routine. -/
structure Effects (K : Contract S) (W : Type) where
  call : K.Call → W → S → W → S → Prop
  ctrl : W → S → W → S → Prop

namespace Effects

variable {K : Contract S} {W : Type} (E : Effects K W)

/-- The effects of an operation. -/
def op {P : Type} : Op K P → W → S → W → S → Prop
  | .ctrl => E.ctrl
  | .call q => E.call q.call

/-- `E_T`, the projection of `Ê_T` on states (Eq. world-projection), for a call. -/
def callE (c : K.Call) (s s' : S) : Prop := ∃ w w', E.call c w s w' s'

/-- `E_ctrl`, the projection of `Ê_ctrl` on states. -/
def ctrlE (s s' : S) : Prop := ∃ w w', E.ctrl w s w' s'

end Effects

/-- **A2 (Coverage of state transitions).** Where a call or the control step is enabled, its model
contains every state its execution can reach. -/
structure Coverage (K : Contract S) {W : Type} (E : Effects K W) : Prop where
  call : ∀ (c : K.Call) (s s' : S), (∃ s'', K.D c s s'') → E.callE c s s' → K.D c s s'
  ctrl : ∀ (s s' : S), (∃ s'', K.ctrl s s'') → E.ctrlE s s' → K.ctrl s s'

theorem Coverage.op {K : Contract S} {W P : Type} {E : Effects K W} (h : Coverage K E)
    {o : Op K P} {w w' : W} {s s' : S} (hen : ∃ s'', o.model s s'') (he : E.op o w s w' s') :
    o.model s s' := by
  cases o with
  | ctrl => exact h.ctrl s s' hen ⟨w, w', he⟩
  | call q => exact h.call q.call s s' hen ⟨w, w', he⟩

/-- An operation as it happens: the world and the state at each of its instants, from its first. -/
structure Segment (W S : Type) where
  Inst : Type
  pt : Inst → W × S
  first : Inst

section

variable (K : Contract S) {P W : Type} (ch : Checker P) (πK : P) (E : Effects K W)

/-- **Executions of the Airlock (A4)**, from the reading `s₀`. Each operation that Algorithms 1–2
choose, for the agent's input, is a segment that starts at the current world and record (i), whose
instants are effects of the operation from there, and whose return gives the next reading (ii). The
indices are the world and the variables when the last operation returned, and the operations so far,
each with its segment. -/
inductive Exec (s₀ : S) : W → Vars K P → List (Op K P × Segment W S) → Prop
  | start (w₀ : W) : Exec s₀ w₀ (PC2.start K s₀) []
  | step {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)} {inp : Input K P}
      {o : Op K P} {κ : S → Vars K P} (σ : Segment W S) (l : σ.Inst) :
      Exec s₀ w x xs → Next K ch πK x inp o κ → σ.pt σ.first = (w, x.record) →
      (∀ τ, E.op o w x.record (σ.pt τ).1 (σ.pt τ).2) →
      Exec s₀ (σ.pt l).1 (κ (σ.pt l).2) (xs ++ [(o, σ)])

/-- **An execution**: the operations that returned, possibly followed by one more that is still
running, or never returns. -/
inductive Execution (s₀ : S) : List (Op K P × Segment W S) → Prop
  | returned {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)} :
      Exec K ch πK E s₀ w x xs → Execution s₀ xs
  | running {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)} {inp : Input K P}
      {o : Op K P} {κ : S → Vars K P} (σ : Segment W S) :
      Exec K ch πK E s₀ w x xs → Next K ch πK x inp o κ → σ.pt σ.first = (w, x.record) →
      (∀ τ, E.op o w x.record (σ.pt τ).1 (σ.pt τ).2) → Execution s₀ (xs ++ [(o, σ)])

variable {K} {ch} {πK} {E}

/-- The variables of an execution are reached by Algorithm 1. -/
theorem Exec.reach {s₀ : S} {w : W} {x : Vars K P} {xs : List (Op K P × Segment W S)}
    (h : Exec K ch πK E s₀ w x xs) : Reach K ch πK s₀ x := by
  induction h with
  | start => exact .start
  | step σ l _ hn _ _ ih => exact .step _ ih hn

end

end PC2

namespace PC2

/-- A property of every element of a list, extended to one more element at its end. -/
theorem forall_append {α : Type _} {P : Nat → α → Prop} {l : List α} {a : α}
    (h₁ : ∀ j (h : j < l.length), P j l[j]) (h₂ : P l.length a) :
    ∀ j (h : j < (l ++ [a]).length), P j (l ++ [a])[j] := by
  intro j hj
  by_cases hlt : j < l.length
  · rw [List.getElem_append_left hlt]; exact h₁ j hlt
  · have heq : j = l.length := by simp at hj; omega
    subst heq
    simpa using h₂

/-- The last element of `l ++ [a]` is `a`, for any property of it. -/
theorem of_getElem_append_length {α : Type _} {l : List α} {a : α} {P : α → Prop}
    (h : P ((l ++ [a])[l.length]'(by simp))) : P a := by
  simpa using h

end PC2
