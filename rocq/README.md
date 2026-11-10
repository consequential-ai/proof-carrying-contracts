# PC2: the Rocq mechanization of the paper

The Rocq mechanization of *Proof-Carrying Contracts: Commitments AI Agents Cannot Break* (one acting
agent, one contract), alongside the [Lean 4 one](../lean/README.md), with the same structure: every
numbered definition, assumption and result of the paper has a Rocq counterpart, listed by paper
number in `Paper.v`.

- Rocq 9.2 with MathComp 2 (`rocq-mathcomp-boot`: ssreflect, `seq`, `eqtype`, `ssrnat`, `bigop`;
  Hierarchy Builder for the few `eqType` instances), the Rocq standard library (`rocq-stdlib`: `lia`,
  strings) and mczify (`rocq-mathcomp-zify`, so that `lia` works on MathComp arithmetic, used only in
  the arithmetic of App. A and App. C). No classical logic, no functional extensionality.
- No `Admitted`, and no axiom at all: `make` runs `Print Assumptions` on every result listed in
  `Paper.v`, and fails unless each one is closed under the global context. (Lean's version uses
  Lean's standard axioms; this one needs none.)
- Assumptions are explicit hypotheses: a theorem's statement lists exactly what it assumes.

Build: `make` (with `rocq` and MathComp on the path, e.g. after `eval $(opam env)`).

Where a docstring says more than its statement proves, the gap is recorded in
[`../GAPS.md`](../GAPS.md), for this mechanization and the Lean one.

## Map

| Paper | File | Main declarations |
|---|---|---|
| §3.1–3.3: tools, contracts, obligations, A3 | `PC2/Basic.v` | `Tool.t`, `Contract.t`, `wp`, `Contract.Adm`, `Obl`, `Win`, `OblN`, `Cert` |
| §3.4, App. B: Algorithms 1–2, A4 (iii), no veto | `PC2/Airlock.v` | `Next`, `Complete`, `Reach`, `call_discipline`, `no_veto` |
| §4.1: effects, A2, A4 | `PC2/Execution.v` | `Effects.t`, `Coverage`, `Segment`, `Exec`, `Execution` |
| §4.1: Lemma 1, Theorem 1 | `PC2/Compliance.v` | `window`, `anytime_compliance` |
| §4.2, §3.5.2: Theorem 2, Proposition 1, agent tools | `PC2/Completion.v` | `StandardForm.t`, `completion`, `settle_obligation`, `send_adm` |
| Example 1: the standard contract | `PC2/Standard.v` | `Standard.Spec.contract`, `Spec.cert`, `Spec.standardForm` |
| §5.1: A5, A6, Theorem 3, Corollary 4 | `PC2/World.v` | `Fidelity`, `Adequacy`, `world_safety`, `completion_in_world`, `deadline` |
| §5.2, App. G, App. F: A7, Lemma G.1, Lemma 2 | `PC2/Isolation.v` | `NI1`, `NI2`, `isolation_stepwise`, `System.isolation`, `ungated_unsafe` |
| §5.4: Theorem 5 | `PC2/Guarantees.v` | `guarantees`, `guarantees_standard`, `guarantees_deadline` |
| §6: Definitions 5–7, Propositions 2–4, Theorem 6 | `PC2/Modules.v` | `CapModule.t`, `tensor`, `Compatible`, `local_to_global_cov`, `custody_guarantees`, … |
| App. A: Eq. (A.1), Proposition A.1 | `PC2/Appendix/WP.v` | `ContractWP.oblN_wp`, `most_permissive_gate`, `decidable_gate` |
| App. C: control design, compute budget | `PC2/Appendix/Control.v` | `Design.cert`, `ComputeBudget.sound` |
| App. D: time between operations | `PC2/Appendix/Gaps.v` | `extend`, `extendK` |
| App. E: payment ledger, booking confirmations | `PC2/Appendix/Ledger.v` | `budget_correspondence`, `booking_correspondence` |
| Table 1 and Fig. 2: the travel contract | `PC2/Examples/Travel.v` | `Travel.cert`, `ep1_book_rejected`, …, `ep4_settle` |

## How the paper is read

As in the Lean mechanization (see its README): executions are runs of Algorithms 1–2 whose
operations are segments of time with abstract instants; A4 (iii) is a lemma; A3 is checked at
startup; the standard contract closes first; isolation is App. G's stepwise formulation; products of
modules are dependent functions over any index type.

## Differences with the Lean mechanization

The statements say what the Lean ones say, written in the MathComp style, with these changes of
representation:

- **Lists** are MathComp sequences: `l[j]?` is `onth l j`, and `l ++ [a]` is `rcons l a`. A
  statement about the `j`-th operation of an execution quantifies over `j` and `p` with
  `onth xs j = Some p`, instead of over `j < xs.length`.
- **The iteration of the last call** is an `option nat`, `None` before the first call (Lean's `-1`),
  and `kLast < j` is `ltl kLast j`.
- **Only settlement changes the label** (standard form) is stated as "a call keeps the label, or is
  settlement", which is Lean's "a call other than settlement keeps the label" without assuming that
  one can decide whether a tool is settlement.
- **Decidable tests are booleans**, used as propositions through `is_true`. `Active K s` is
  `~~ stop K s`, and "inactive" is `stop K s` (Lean's `¬ K.Active s`). The test of Algorithm 1,
  line 9, is the boolean `authorized`. The verdict phases and the travel contract's visa and escrow
  have an `eqType`. The travel contract's constraints `B` and goal `Goal` are boolean tests, so the
  facts about the states of Fig. 2 are proved by computation. App. A's decidable gate *reflects* the
  obligation (`reflect (OblN K n c v) (g c n v)`).
- **Conjunctions** of three to five parts are written `[/\ a, b & c]` (and `[\/ a, b | c]` for
  disjunctions), and two-sided bounds are chained (`k₀ q <= k <= k₀ q + allow q`). What a step of
  Algorithm 1 leaves unchanged is an equation of variables (`complete_eq`, `step_eq`), not a
  conjunction of field equalities. Outside changes in the travel contract are a record (`out`) with
  named fields.
- **Sums** are MathComp big operators: App. E sums with `\sum_(j <- ids) f j` and uses `leq_sum`.
- **Names.** Records live in modules (`Tool.t`, `Contract.t`, `Effects.t`, `StandardForm.t`,
  `CapModule.t`, `System.t`), so the Lean names stay (`Tool.adm_iff`, `Contract.OblN`,
  `System.isolation`). `Module` and `End` are Rocq keywords: the capability module is `CapModule.t`,
  and the set `End` of the standard form is `Ends`. Lean's `Contract.settle_obligation` is
  `settle_obligation`, App. A's results are in `ContractWP`, App. D's extensions are `extend` and
  `extendK`. The fields of the effects are `ecall` and `ectrl` (Lean's `call` and `ctrl`), so that
  they do not clash with a request's call and the contract's control step. Lemma names start with a
  lowercase letter (`reach_wf`, `exec_reach`, `coverage_op`, `prefix_trans`), and the two reach
  relations of App. G are one `reachBy` for two step relations.
- **Function equality** is never used: where Lean rewrites with an equality of step relations
  (`refStep_agent`), the Rocq proof transports prefixes along an implication between them.

Theorem 1, as stated:

```coq
Theorem anytime_compliance (hA1 : Checker.Sound ch) (hA2 : Coverage K E) {s₀ : S}
    {xs : seq (Op K P * Segment W S)} :
  Execution K ch πK E s₀ xs ->
  forall j p, onth xs j = Some p -> forall τ : Inst p.2,
    (0 < j \/ Active K (pt p.2 τ).2) -> C K (pt p.2 τ).2.
```

For any sequence of requests and proofs, every execution satisfies the clause at every instant of
every operation from the start of the contract (at the active instants of the initialization, and at
every instant after it), throughout an operation that never returns as well.
