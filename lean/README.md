# PC2: the mechanization of the paper

The Lean 4 mechanization of *Proof-Carrying Contracts: Commitments AI Agents Cannot Break* (one acting
agent, one contract). Every numbered definition, assumption and result of the paper has a Lean
counterpart, listed by paper number in `Paper.lean`.

- Lean 4.35.0, core library only: no Mathlib, no Iris, no IO.
- No `sorry`. The build checks the axioms of every theorem (`Paper.lean`): each depends at most on
  Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and the build fails otherwise.
- Assumptions are explicit hypotheses: a theorem's signature lists exactly what it assumes.

Build: `lake build` (about 4 seconds).

## Map

| Paper | File | Main declarations |
|---|---|---|
| §3.1–3.3: tools, contracts, obligations, A3 | `PC2/Basic.lean` | `Tool`, `Contract`, `wp`, `Adm`, `Obl`, `Win`, `OblN`, `Cert` |
| §3.4, App. B: Algorithms 1–2, A4 (iii), no veto | `PC2/Airlock.lean` | `Next`, `Complete`, `Reach`, `call_discipline`, `no_veto` |
| §4.1: effects, A2, A4 | `PC2/Execution.lean` | `Effects`, `Coverage`, `Segment`, `Exec`, `Execution` |
| §4.1: Lemma 1, Theorem 1 | `PC2/Compliance.lean` | `window`, `anytime_compliance` |
| §4.2, §3.5.2: Theorem 2, Proposition 1, agent tools | `PC2/Completion.lean` | `StandardForm`, `completion`, `Contract.settle_obligation`, `send_adm` |
| Example 1: the standard contract | `PC2/Standard.lean` | `Standard.Spec.contract`, `Spec.cert`, `Spec.standardForm` |
| §5.1: A5, A6, Theorem 3, Corollary 4 | `PC2/World.lean` | `Fidelity`, `Adequacy`, `world_safety`, `completion_in_world`, `deadline` |
| §5.2, App. G, App. F: A7, Lemma G.1, Lemma 2 | `PC2/Isolation.lean` | `NI1`, `NI2`, `isolation_stepwise`, `System.isolation`, `ungated_unsafe` |
| §5.4: Theorem 5 | `PC2/Guarantees.lean` | `guarantees`, `guarantees_standard`, `guarantees_deadline` |
| §6: Definitions 5–7, Propositions 2–4, Theorem 6 | `PC2/Modules.lean` | `Module`, `tensor`, `Compatible`, `local_to_global_cov`, `custody_guarantees`, … |
| App. A: Eq. (A.1), Proposition A.1 | `PC2/Appendix/WP.lean` | `oblN_wp`, `most_permissive_gate`, `decidable_gate` |
| App. C: control design, compute budget | `PC2/Appendix/Control.lean` | `Design.cert`, `ComputeBudget.sound` |
| App. D: time between operations | `PC2/Appendix/Gaps.lean` | `Tool.extend`, `Contract.extend` |
| App. E: payment ledger, booking confirmations | `PC2/Appendix/Ledger.lean` | `budget_correspondence`, `booking_correspondence` |
| Table 1 and Fig. 2: the travel contract | `PC2/Examples/Travel.lean` | `Travel.cert`, `ep1_book_rejected`, …, `ep4_settle` |

## How the paper is read

- **Executions.** An execution is a run of Algorithms 1–2 in which every operation is a segment of time:
  the world and the state at each of its instants. Instants are abstract (any type: real time, ticks); no
  property of time is used. A4 is the statement that the actual execution is one of these.
- **Effects.** What a routine does enters through the effects `Ê` of the deployment; `E` is their
  projection on states. Coverage (A2) and fidelity (A5) are conditions on them.
- **Algorithms 1–2** are a transition system at the level of operations. Requests are inputs, and when a
  running check finishes is left open: the runs cover every sequence of requests and proofs and every
  interleaving of the parallel checker with the loop. A4 (iii) is a lemma, not an assumption.
- **A3 is checked at startup.** The Airlock starts only if the checker accepts the certificate as a proof
  of A3 (Algorithm 1, line 2), so with A1 the theorems do not assume it.
- **The standard contract closes first.** Settlement and termination change the label when they start;
  the payment or the refund then runs with the contract closed. No reserve of time is needed. Under a
  deadline, every task tool's model bounds its duration (its timeout).
- **Every agent.** Isolation (A7) is App. G's stepwise formulation (NI1, NI2). The effects with an agent
  are among the reference effects (Lemma 2), so A2 and A5 are assumed only for reference executions.
- **Modules.** Products are taken over any index type, as dependent functions.

Theorem 1, as stated:

```lean
theorem anytime_compliance (hA1 : ch.Sound) (hA2 : Coverage K E) {s₀ : S}
    {xs : List (Op K P × Segment W S)} (hX : Execution K ch πK E s₀ xs) :
    ∀ j (h : j < xs.length) (τ : xs[j].2.Inst),
      (0 < j ∨ K.Active (xs[j].2.pt τ).2) → K.C (xs[j].2.pt τ).2
```

For any sequence of requests and proofs, every execution satisfies the clause at every instant of every
operation from the start of the contract (at the active instants of the initialization, and at every
instant after it), throughout an operation that never returns as well.
