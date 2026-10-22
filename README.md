# Proof-Carrying Contracts (PC2)

This repository accompanies the paper
[**Proof-Carrying Contracts: Commitments AI Agents Cannot Break**](https://arxiv.org/pdf/2610.28484)
by Carlo Ciliberto, Alessandro Rudi, and Enrico Tassi.

## Mechanization and code

The Lean 4 mechanization of the paper is in [`lean/`](lean/README.md). It
states the paper's definitions, assumptions and results and proves them, with
no `sorry`. [`lean/Paper.lean`](lean/Paper.lean) lists the Lean statement of
each numbered item of the paper, and checks at build time that no theorem
depends on axioms beyond Lean's standard ones.

To check it, install [elan](https://github.com/leanprover/elan), then run:

```sh
cd lean
lake build   # Lean 4.35.0, core library only
```

Further code accompanying the paper will be released in this repository.

## Citation

```bibtex
@misc{ciliberto2026proofcarryingcontracts,
  title = {Proof-Carrying Contracts: Commitments {AI} Agents Cannot Break},
  author = {Carlo Ciliberto and Alessandro Rudi and Enrico Tassi},
  year = {2026},
  eprint = {2610.28484},
  archivePrefix = {arXiv},
  url = {https://arxiv.org/pdf/2610.28484}
}
```

## Project website

See the [PC2 website](https://consequential-ai.github.io/proof-carrying-contracts/)
for an introduction to the project. Website source and maintenance instructions
are in [`website/`](website/README.md).
