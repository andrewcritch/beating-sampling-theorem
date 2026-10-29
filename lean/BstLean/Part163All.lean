import BstLean.Part163Comb
import BstLean.Part163Sane
import BstLean.Part163Bias
import BstLean.Part163Vac
import BstLean.Part163Prob
import BstLean.Part163Vac2

/-!
# Part 163: the top module

Do not use `sorry`, `native_decide` or `axiom`.

* `Part163Comb`: the correct combination of Parts 159 and 160 (`classifier_paper_free23`).
* `Part163Sane`: the repaired good set excludes `A₂ = 0`; the old one contains it.
* `Part163Bias`: the combination with Parts 161 and 162 (`classifier_paper_free23_psi12e`).
* `Part163Vac`: the hypothesis of Part 160's `classifier_paper_comb23` is false
  (`comb23_hyp_false`).
* `Part163Prob`: the free-event theorem in probability form (`classifier_paper_free23_prob`).
* `Part163Vac2`: the hypotheses of Part 162's `classifier_paper_mom` and `classifier_paper_psi` are false.
-/
