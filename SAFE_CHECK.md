# A verified checker for the extracted Airlock, with MetaRocq

This is a design note: nothing in it is built. It says how MetaRocq could give the Airlock a
checker that still means something after extraction. MetaRocq has a *SafeChecker*, a verified type
checker for Rocq terms, and the file's name refers to it. The note concerns the Rocq mechanization
only. MetaRocq is not a dependency of this repository.

Claims about MetaRocq's exact module names and hypotheses (the project was renamed from MetaCoq to
MetaRocq) are stated generically. Check them against the MetaRocq version you install.

## 1. The problem

`rocq/PC2/Program.v` makes Algorithms 1–2 a Rocq function, `step`/`run`. Its checker is abstract
(`rocq/PC2/Airlock.v:32–37`):

```coq
Record t (P : Type) := Build { accepts : P -> Prop -> bool }.
Definition Sound (P : Type) (ch : t P) : Prop :=   (* A1 *)
  forall (π : P) (Φ : Prop), accepts ch π Φ -> Φ.
```

Inside Rocq this is fine. Extraction, however, erases `Prop`, so the extracted `accepts` receives
nothing in place of the statement. The program calls it on `Cert K` and on `OblN K n c v`
(`checkOK`, `Airlock.v:125`). Once extracted, it cannot tell what it is asked to check. It could
only accept everything, or nothing.

The fix: the statement the checker reads must be *data*, and the checker must be a program whose
soundness is a theorem rather than an assumption.

## 2. What MetaRocq provides

- **Quoting.** A Rocq term becomes a value of an inductive type of syntax (`Ast.term`), and
  unquoting goes back. `tmQuote`/`tmQuoteRec` quote a term, the latter together with the global
  environment it depends on (`global_env`).
- **PCUIC.** A cleaned-up calculus for Rocq's theory, with its typing judgment
  `Σ ;;; Γ |- t : T` and a verified translation from the quoted syntax.
- **The SafeChecker.** A type checker for PCUIC, written in Rocq, proved sound and complete for
  PCUIC typing, and extractable to OCaml.
- **Verified erasure.** A proved-correct erasure of Rocq programs to an untyped calculus (λ□),
  from which OCaml or Malfunction code can be produced.

## 3. The design

### Statements as data

Instantiate the checker at the syntax:

```coq
accepts : term -> term -> bool          (* proof, statement *)
accepts π φ := <SafeChecker: Σ ;;; [] |- π : φ>
```

Proofs are terms, so `P := term`. `Program.v` is parametric in the checker, so it needs no change.
`Checker.t` needs one: it must allow statements of a type other than `Prop`, for instance a
statement type with a denotation `⟦_⟧ : Stmt -> Prop`, and A1 stated as `accepts π φ -> ⟦φ⟧`.

### The environment

`Σ` is the quoted global environment of the contract: `K`, `OblN`, `wp`, the tool models, and what
they rely on. It is built once with `tmQuoteRec`, and its well-formedness is checked once, offline.
At run time the checker only types terms in this fixed `Σ`.

### The obligation as a function

The checker must build the statement it checks. Quote the obligation once, as an open term:

```coq
T_obl := ⌜fun n c v => OblN K n c v⌝
obl_stmt n c v := tApp T_obl [⌜n⌝; ⌜c⌝; ⌜v⌝]
```

Here `⌜_⌝` are reifiers for the concrete first-order data that `step` handles: numbers, strings,
calls, views. They are plain Rocq functions such as `nat -> term`. `Cert K` is a single quoted
closed term. In the extracted program, `checkOK` calls `accepts (π q) (obl_stmt …)`.

### Agents still prove with tactics

The agent works in ordinary Rocq, against the same definitions. It proves the obligation with
tactics, closes it with `Qed`, quotes the proof term with `tmQuoteRec`, and sends the resulting
`Ast.term`. The checker never sees a tactic. Some care is needed:

- **Dependencies.** The proof term refers to constants: library lemmas and the agent's own helper
  lemmas. Those not already in `Σ` travel with the term. They are checked too, and added to a
  per-proof extension of `Σ`.
- **Axioms.** The checker rejects any axiom declaration in what it receives, unless the axiom is on
  an explicit whitelist. Otherwise an agent could ship `Axiom cheat : False`.
- **Statements.** The checker checks `π` against *its own* `obl_stmt n c v`, never against the
  statement the agent claims. The two need only be convertible.
- **Cost.** Proofs by reflection (`by []`, `vm_compute` casts) become plain conversion checks, run
  by the SafeChecker without a virtual machine, so they can be slow. Primitive integers and arrays
  may be unsupported, depending on the version. Terms coming from MathComp proofs can be large.

### Algorithm 2 runs in parallel

`Program.v` models the parallel checker as an oracle, `CheckEv := Busy | Done (ok : bool)`, one
event per iteration. In the extracted program, the oracle is an OCaml thread running the
SafeChecker. It reports `Busy` until the check returns, and `Done ok` after. `run_sound`
(`Program.v`) then says that every run of this program is a run of Algorithm 1, whatever the
thread's timing.

### The loop itself

The Airlock loop can be compiled with MetaRocq's verified erasure instead of Rocq's unverified
`Extraction`. The loop is then covered by a proof down to λ□: both the code that decides and the
code that runs.

## 4. What is proved and what is trusted

**Proved, by MetaRocq:**
- SafeChecker soundness: `accepts π φ = true -> Σ ;;; [] |- π : φ`;
- correctness of the translation from quoted syntax to PCUIC, and of erasure.

**Proved, here (to do):**
- the reifiers are correct: unquoting `⌜x⌝` gives `x`;
- `obl_stmt` agrees with `OblN`: unquoting `obl_stmt n c v` gives `OblN K n c v`. For a concrete
  contract this follows by computation, from `T_obl`'s construction by quotation.

**The gap: A1 is reduced, not removed.** A1 asks for the proposition `OblN K n c v` itself. The
SafeChecker gives only a PCUIC typing derivation `Σ ;;; [] |- π : φ`. Concluding `⟦φ⟧` from it
means trusting that typable PCUIC terms denote true Rocq propositions. Rocq cannot prove this about
itself, since it would prove its own consistency (Gödel). A1 therefore remains an assumption, but
it shrinks from "an arbitrary checker is sound" to the following trusted base:

- PCUIC's typing rules, as a faithful specification of Rocq's theory;
- the hypotheses the SafeChecker's proof rests on, chiefly strong normalization of PCUIC, which
  Rocq cannot prove internally, and an abstract guard condition for fixpoints;
- the quotation of `Σ`, that is, that the quoted contract is the contract;
- the OCaml compiler and runtime, for the extracted code.

This base is standard and much smaller than "an arbitrary checker".

**Effect on `Paper.v`.** The SafeChecker's soundness depends on its hypotheses. A result that
imports it is therefore no longer "closed under the global context", the property that
`rocq/Paper.v` and the Makefile enforce. The instantiation belongs in its own directory (say
`rocq/extract/`), outside the axiom-free list. The paper's theorems stay as they are: they are
stated for any sound checker.

## 5. Steps

1. Add MetaRocq as an optional dependency, used only by `rocq/extract/`.
2. Let `Checker.t` take statements of any type, with a denotation, and restate A1 through it.
   This is a small change to `Airlock.v`; `Program.v` is unchanged.
3. Quote `Σ` and `T_obl` for the compute-budget contract (`rocq/PC2/Appendix/Control.v`). Write the
   reifiers and `obl_stmt`, and prove their agreement with `OblN`.
4. Instantiate `accepts` with the SafeChecker. Add the axiom filter and the handling of shipped
   dependencies.
5. Extract or erase `run`. Write an OCaml driver: agent input, readings from a stub world, and
   Algorithm 2 in a thread.
6. Test it end to end, with an agent proof written with tactics, quoted, and sent.

## 6. Limits

- Agents must send terms, not scripts. A tactic proof is fine, but only its term travels.
- The SafeChecker is slower than Rocq's kernel, and has no virtual machine or native compiler.
- It may not cover every kernel feature, for example some primitive types or sort polymorphism.
  Proofs using them would be rejected, which is safe but incomplete.
- Only the Airlock becomes a program. The world side (`Exec`, the effects, the correspondence `ρ`)
  stays relational: it is the environment, not code.
- There is no Lean counterpart. Lean has independent kernel replays of its own, but none comparable
  is verified, and the Lean mechanization has no executable Airlock (`LOGIC.md`).
