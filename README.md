# Beating Sampling: Mechanistic Estimation of the Failure Rate of a Neural Network at Frontier Scale

Andrew Critch (MAISI)

This repository contains the paper ([`paper/main.pdf`](paper/main.pdf)) and its Lean 4 formalization ([`lean/`](lean/)).

## Abstract

When can the failure rate of a neural network be estimated more efficiently by analyzing its internals than by sampling its outputs? We investigate this question for a class of random ReLU MLP "agents", and prove that the answer is "usually", with a single explicit estimation procedure which upper-bounds the failure rate *p* within a factor of 10, or else by at most 1%, for at least 99% of networks and random seeds. The result holds for every input dimension *n* ≥ 8,000. For agents in our class with 8,000 ≤ *n* ≤ 16,384 (comparable to the embedding width of current frontier transformers), with between 4.1·10¹⁵ and 7.2·10¹⁶ parameters, the procedure costs about as much as a single exact sample of the agent's behavior. By contrast, consider a naive estimator that sees only the outcomes of exact samples and must succeed with probability 0.99 for every value of the failure rate *p*. When *p* ≤ 0.1%, the naive estimator needs more than 448 samples on average. For such low failure rates, our procedure is thus more than 447 times more efficient than naive sampling. The Beating Sampling Theorem and its proof are checked in Lean, and the translation of the Beating Sampling Theorem's assumptions and conclusions into Lean has been checked by GPT-6-Astra (high effort) and Claude Opus 5.5 (medium effort).

## The Lean theorems

The root file [`lean/BSP.lean`](lean/BSP.lean) imports the modules that state the two final results:

- `BstLean.Part293.classifier_stated2_8000` (in `BstLean/Part293FinalAudit.lean`): for every `n ≥ 8000` and every real `t`, the estimator succeeds, i.e., `p ≤ U ≤ max (10 p) (1/100)`, with probability at least `99/100` over the three random networks and the estimator's random seed.
- `BstLean.Part289.progOut_run2` (in `BstLean/Part289Cost.lean`): for every `n ≥ 8000` and every input, a counted program returns the same output and uses fewer than `1.0003 · 2 n⁷` operations.

`BSP.lean` checks with `#guard_msgs` that both theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Building the Lean project

The project uses Lean `v4.34.1` and Mathlib `v4.34.1` (see `lean/lean-toolchain` and `lean/lakefile.toml`). With [elan](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build           # build BstLean and BSP
```

**The build is long.** The project has 5,833 modules. On a Mac mini with 16 GB of memory, a full build from scratch took between 2.5 and 4 days, with a peak memory use of about 7 GB. A successful build ends with `Build completed successfully`, and the `#guard_msgs` checks in `BSP.lean` fail the build if either theorem uses another axiom.

## Repository layout

- `paper/`: the paper.
  - `main.tex`, `steps.tex`, `appendix.tex`, `main.pdf`.
  - `make-pdf.sh`: builds `main.pdf` with [Tectonic](https://tectonic-typesetting.github.io/). `./make-pdf.sh --all` first regenerates the appendix table of Lean files and runs the coverage check.
  - `groups.py`: the named groups of Lean modules that the paper's appendix lists.
  - `gen_appendix.py`: generates `appendix.tex` from `groups.py`.
  - `check_coverage.py`: checks, without running Lean, that every module of the Lean project is cited in the paper, directly or through a group.
- `lean/`: the Lean project.
  - `BSP.lean`: the root file and the axiom checks.
  - `BstLean/`: the 5,833 modules.
  - `closure.txt`: the list of all modules.
  - `reports/depmap.tsv`: for each module, the number of its declarations that the two final theorems use (4,290 modules have at least one). `tools/DepMap.lean` generates it.

Some Lean docstrings name files from the private working repository in which the proofs were developed, such as specifications under `delegations/`. Those files are not part of this repository, and the Lean source is the authority.

## License

MIT; see [`LICENSE`](LICENSE).
