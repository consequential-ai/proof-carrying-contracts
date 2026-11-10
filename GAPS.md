# Gaps between the mechanizations and their prose

Places where a docstring (and, through it, the paper's wording) says more than the mechanized
statement proves. Every gap below is present in both the Rocq and the Lean mechanization. No
statement has been changed to close them. Each entry gives what is claimed, what is proved, and a
suggested fix.

All results listed in `rocq/Paper.v` are proved and closed under the global context. The gaps are
about the prose, not about missing proofs.

## 1. Theorem 2, void case: "the conditions to start did not hold"

- **Rocq:** `rocq/PC2/Completion.v:101–116` (`completion`), case 1 of the docstring.
- **Lean:** `lean/PC2/Completion.lean:95–107` (`completion`), case 1 of the docstring.
- **Claimed:** if the last reading is *void* (or still *pending*), "the conditions to start did not
  hold, and no tool call was made".
- **Proved:** only the second half. If the label is `Pending` or `Void`, every operation of the
  execution is a control step (`p.1 = OpCtrl`). Nothing about `Ready` is stated.
- **Fix, either:**
  - strengthen the void case with `~ Ready F s₀`. The standard form already provides it:
    `ctrl_pending` gives `lab s' = Void /\ ~ Ready s` at the initialization step
    (`Completion.v:58`, `Completion.lean:44`). The proof's initialization branch has that fact in
    hand. The non-initialization branches need an invariant that the label never returns to
    `Void` once `Ongoing`.
  - or reword the docstring to "no tool call was made".
- **Also repeated in:** Theorem 5 (2)–(3), "Theorem 2 (1) gives the third way, void"
  (`rocq/PC2/Guarantees.v:36`, `lean/PC2/Guarantees.lean:33`).

## 2. Theorem 2: "in exactly one way"

- **Rocq:** `rocq/PC2/Completion.v:102–103`.
- **Lean:** `lean/PC2/Completion.lean:96–97`.
- **Claimed:** the label of the last reading says how the contract ended "in exactly one way".
- **Proved:** three implications, one per label value. Exclusivity is not stated. It follows at
  once from the labels being distinct constructors.
- **Fix:** none needed for correctness. Either say "the label says which of three ways", or add a
  one-line corollary that at most one premise holds.

## 3. Theorem 5 (4): "Settlement or termination has begun by d"

- **Rocq:** `rocq/PC2/Guarantees.v:58–61` (`guarantees_deadline`); the underlying statement is
  `rocq/PC2/World.v:169–172` (`deadline`).
- **Lean:** `lean/PC2/Guarantees.lean:52–55` (`guarantees_deadline`); `lean/PC2/World.lean:171–174`
  (`deadline`).
- **Claimed:** past the deadline the contract is not active, and "settlement or termination has
  begun by `d`".
- **Proved:** only that the contract is inactive (`stop K s` in Rocq, `¬ K.Active s` in Lean). The
  theorem is about any contract, so it has no label. For a standard contract, "inactive" also
  covers `Pending` and `Void`, that is, a contract that never started.
- **Fix, either:**
  - add a standard-form corollary: under `StandardForm`, if the contract was once `Ongoing` and is
    now inactive, its label is `Settled` or `Terminated`. That needs the same "never back to
    `Pending`/`Void`" invariant as gap 1.
  - or reword to "the contract is no longer active by `d`".

## 4. Capability modules: "regrouping and permuting the factors is reindexing"

- **Rocq:** `rocq/PC2/Modules.v:8–9` (file header).
- **Lean:** `lean/PC2/Modules.lean:10–11` (file header).
- **Claimed:** regrouping and permuting the factors of a product of modules is a reindexing of the
  index type.
- **Proved:** nothing. Products are dependent functions over an arbitrary index type, which makes
  the remark plausible, but no lemma relates `tensor M sel` to its reindexing along a bijection of
  `ι`.
- **Fix:** add a lemma (for a bijection `e : ι' -> ι`, `tensor (M \o e) (sel \o e)` has the same
  models as `tensor M sel` up to `e`). Or mark the sentence as an informal remark.

## Checked, not gaps

- **App. D, "every result of the paper applies to [𝒦']"** (`rocq/PC2/Appendix/Gaps.v:5`,
  `lean/PC2/Appendix/Gaps.lean:8`). `extendK` is a `Contract`, and every theorem is stated for an
  arbitrary contract, so this holds by instantiation, "with its own assumptions" as the docstring
  says. `rocq/Paper.v` now lists `extendK`.
- **A7 (ii), "holds by construction"** (`rocq/PC2/Isolation.v`, `lean/PC2/Isolation.lean`). The
  docstring says so explicitly, and the model gives the routine's initial state from the call
  alone.
