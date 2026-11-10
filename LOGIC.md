# Decidability and axioms in the mechanizations

This note says which facts of the paper are *tests*, decided by computation, and which are
*propositions*, and which axioms each mechanization relies on. It covers the Rocq mechanization
(`rocq/`) and, for comparison, the Lean one (`lean/`).

## Principle (Rocq)

The Rocq mechanization is constructive: it uses no axioms, not even excluded middle. `rocq/Paper.v`
prints the assumptions of every result, and the build fails unless each one is "Closed under the
global context".

It follows MathComp in separating two kinds of facts:

- **Tests.** A decidable fact is a `bool`. Predicates are `pred T` (`T -> bool`) and relations
  `rel T`. Tests combine with `&&`, `||`, `==>`, `[&& …]`, `[|| …]`, and with `==` on types that
  have an `eqType` instance. Where a `Prop` reading helps a proof, a reflection lemma
  (`reflect P b`, named `…P`) relates the two.
- **Propositions.** A fact that quantifies over states, executions or world states stays a `Prop`.

**No type parameter carries a structure.** The state spaces, world states, views, proofs, tool
names and tool inputs are arbitrary types (`Type`). No theorem asks any of them for an `eqType`,
`choiceType` or `countType` instance. `==` is used only on concrete types, each with its own
`eqType` instance (`Equality.axiom` + `hasDecEq.Build`):

| Type | Where | Used for |
|---|---|---|
| `Phase` | `rocq/PC2/Airlock.v` | where the loop is |
| `Label` | `rocq/PC2/Completion.v` | the contract label of the standard form |
| `string` | `rocq/PC2/Examples/Travel.v` | hotels, recipients (from `String.eqb_spec`) |
| `Visa`, `Escrow` | `rocq/PC2/Examples/Travel.v` | the travel state |

`nat`, and lists and pairs of these, inherit their instances from MathComp.

## What is a test

| Concept | Rocq | Why it is decidable |
|---|---|---|
| Inactivity `stop`, activity `Active := ~~ stop` | `S -> bool` | Algorithm 1 evaluates it at every iteration |
| The clause `C` | `pred S` | control and the certificate evaluate it on states |
| Business constraints `B`, goal `Goal` | `pred X` | the standard contract's clause and settlement precondition are built from them |
| Control's tests `Ready`, `Act`, `Fix`, `Ends`, `endX` | `bool` | the routine of §3.5.1 branches on them |
| The precondition `Pre` of `T\|Pre` | `Inp T -> pred S` | a precondition is checked before the call |
| Checker acceptance `accepts` | `P -> Prop -> bool` | a checker is an algorithm; A1 relates it to truth |
| Algorithm 2's `check` (`checkOK`), line 9 (`authorized`) | `bool` | they are steps of the algorithms |
| Compute budget: `C`, `idle`, `shut` | `pred`, `rel` | arithmetic on the state; the waiting time is `time s' - time s` |
| Travel: `B`, `Goal`, `readyX`, `out` | `pred`, `rel` | finite data: numbers, strings, lists |

Abstract parameters that are tests (the clause, `B`, `Goal`, the tests of the standard form, the
precondition, the checker) are tests in every theorem. A consequence follows below.

## What stays a proposition

| Concept | Why |
|---|---|
| Tool models `Tool.D`, the control model `ctrl`, the effects, the standard contract's `pay`, `initX`, `voidX`, `out`, `refund` (in general), routines | nondeterministic specifications, often with an `exists` over outside changes or world states. Concrete instances are `rel` where decidable (`idle`, `shut`, Travel's `out`) and are passed to these fields by eta-expansion |
| `wp`, `En`, `Dem`, `Adm`, `Obl`, `OblN`, `Win`, `Kn`, `Cert`, `SafeGate` | they quantify over all states. App. A shows that obligations are undecidable in general (`decidable_gate`) |
| Runs and invariants: `Reach`, `Run`, `Exec`, `Execution`, `Next`, `Complete`, `Chk`, `Wf`, `Inv`, `Prefix` | inductive relations over executions |
| Assumptions A2 and A5–A7: `Coverage`, `Fidelity`, `Adequacy`, `Isolation`, `A7` | quantify over executions and world states |
| The world side: the correspondence `ρ`, `Safe`, `GoalW`, the ledger's `forall j` facts, `bookingρ`, the module registers | facts about the physical world, over arbitrary index types |

## Consequence

The Rocq theorems are stated for decidable clauses, goals, preconditions and checkers. No proof
needs this: it is a modelling choice, matching the algorithms, which evaluate these tests. The Lean
mechanization takes `Prop` predicates, so its theorems are more general on this point. Each of its
uses on a decidable predicate, as in the travel example, comes with a `DecidablePred` instance.

## The Airlock as a program (Rocq only)

Because every test of Algorithms 1–2 is a boolean, Algorithm 1 is a function once two inputs
are given: the agent's input, and Algorithm 2's progress at each iteration (`CheckEv`: the
check is still busy, or it has finished). This turns the parallel checker into an oracle; the
loop reads the verdict only at line 9, so the oracle covers every interleaving.

`rocq/PC2/Program.v` defines the iteration `step` and the run `run`, and proves that they
implement the relations of `rocq/PC2/Airlock.v`:
- `nextP` relates `step` and `Next` in both directions;
- `run_sound`/`run_complete` relate `run` and `Run`;
- `reach_run` relates `run` and `Reach`.

The program returns the same continuations as the relation, so no functional extensionality is
needed. An example computes a run of the compute-budget contract.

The Lean mechanization has no counterpart. There, the checker's acceptance is a proposition
(`accepts : P → Prop → Prop`, `lean/PC2/Airlock.lean:41`), and so is what Algorithm 2's check
computes, so an executable step would first need acceptance to be decidable. Running the program
outside Rocq, by extraction, would need more in both mechanizations:
- the statements the checker reads would have to be data, not propositions;
- the state, the views and the calls would have to be concrete types.

## Why Lean derives `DecidableEq`

Lean derives `DecidableEq` on six types. Each instance has a use:

- **`Phase`** (`lean/PC2/Airlock.lean:70`) and **`Actor`** (`lean/PC2/Isolation.lean:35`):
  - the proofs split cases with `by_cases hinit : x.phase = .init` (`Completion.lean:120`,
    `World.lean:64, 90`) and `by_cases hb : b = .agent` (`Isolation.lean:81`);
  - Lean core's `by_cases` uses a `Decidable` instance when there is one, and otherwise falls
    back to `Classical.propDecidable`, which makes the result depend on `Classical.choice`;
  - a probe confirms it: `by_cases` on a `Phase` equality depends on no axiom, while the same
    split on an equality in an arbitrary type depends on `Classical.choice`.
- **`Label`** (`lean/PC2/Completion.lean:21`):
  - `by decide` proves that distinct constructors differ (`Completion.lean:81–93`);
  - the standard contract's `stop s := s.ℓ != .ongoing` (`Standard.lean:131`) uses the
    Boolean `!=` that the instance provides.
- **`Visa`**, **`Escrow`** and the travel state **`X`** (`lean/PC2/Examples/Travel.lean:25, 32,
  48`):
  - `==` in `Ready` and `endX` (`Travel.lean:120, 127`);
  - `decide` in the Fig. 2 facts.
  - `DecidablePred B` and `DecidablePred Goal` (`Travel.lean:66, 71, 130–131`) let `decide`
    evaluate the constraints and the goal.
  - `String`'s instance (from Lean core) runs `lookup`'s `if h' = h`.

In Rocq, the `eqType` instances above play the same roles, and computation (`by []`) replaces
`decide`.

## Axioms in Lean

`lean/Paper.lean` checks the axioms of every result. Lean's standard axioms are `propext`,
`Quot.sound` and `Classical.choice`. Seven results depend on `Classical.choice`:

- `anytime_compliance`
- `completion`
- `world_safety`
- `completion_in_world`
- `guarantees`
- `guarantees_standard`
- `guarantees_deadline`

The dependency comes from two features of the tactics, not from the mathematics:

1. **`omega` on a goal that is not arithmetic.** `omega` argues by contradiction on its goal, which
   is classical unless the goal is decidable. A probe shows it: `0 < j → j = 0 → Q` proved by
   `omega` depends on `Classical.choice`, and proved by `exfalso; omega` it does not. Two places do
   this:
   - the last branch (`.ctrlAfterCall`) of `next_inv` (`Compliance.lean:179`), and through it
     `exec_inv`;
   - `segment_faithful` (`World.lean:68`).

   Fix: `exfalso; omega`.
2. **A case split on tool names.** `completion` uses `by_cases hs : q.call.1 = F.settle`
   (`Completion.lean:145`), and tool names have no `DecidableEq`. This is because the standard
   form states `tools_label` with the premise `c.1 ≠ settle` (`Completion.lean:40`).

   Fix: state it as a disjunction, `lab s' = lab s ∨ c.1 = settle`, as the Rocq mechanization
   does. Alternatively, assume `DecidableEq K.Name`.

With both fixes, no Lean result would depend on `Classical.choice`. The Lean sources have not been
changed; `GAPS.md` lists this too.
