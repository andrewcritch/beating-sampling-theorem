import BstLean.Part161Defs
import BstLean.Part161Root
import BstLean.Part161Split
import BstLean.Part161Gauss
import BstLean.Part161Lat
import BstLean.Part161Tail
import BstLean.Part161Red
import BstLean.Part161Chi
import BstLean.Part161Fl
import BstLean.Part161Final
import BstLean.Part161Cor
import BstLean.Part161Six

/-!
# Part 161: the Agent replacement hypothesis `REPLA_mix_hyp` of the classifier theorem

This module imports every file of Part 161. See `delegations/answers/p161-spec-opus.md`.

* `Part161Defs`: shared definitions.
* `Part161Root`: the Hellinger root comparison, `H² ≤ χ²`, the mixture inequality (item 1(a)).
* `Part161Split`: the split of the root (Lemma `t7:p07:split`, item 1(d)).
* `Part161Gauss`: the Gaussian formulas in `ℝⁿ` (item 1(b)), the two-copy integral.
* `Part161Lat`: the latitude decomposition of the stand-in input (Lemma `t7:p07:latitude`).
* `Part161Tail`: the latitude tail (Lemma `t7:p07:tails`, item 3).
* `Part161Red`: the reduction of `REPLA_mix_hyp` to `FLUCT_hyp` and `BIAS_hyp` (item 2).
* `Part161Chi`: the two-copy identity and the root bound for a Gaussian mixture (item 1(c)).
* `Part161Fl`: `FLUCT_chi_hyp` (scalar fluctuations of `(λ, S)`) gives `FLUCT_hyp`.
* `Part161Cor`: the second-order bound of the chi-square (Corollary `t7:p07:chi-bounds`,
  general conclusion).
* `Part161Six`: the centred sixth-order bound (formula `t7:p07:chi-six`).
* `Part161Final`: Part 159's classifier theorem with `REPLA_mix_hyp` replaced by
  `FLUCT_chi_hyp`, `BIAS_hyp` and `E₁ ⊆ E_{θ−} ∩ E_{θ+}`.
-/
