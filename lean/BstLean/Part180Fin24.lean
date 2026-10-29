import BstLean.Part180End
import BstLean.Part180HQS

/-!
# Part 180 (file `Fin24`): the unconditional classifier theorem for every `n ≥ 24 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_nocap24`**: Part 172's conclusion for every `n ≥ 24 000` and every
  `t`, with no hypothesis: file `End`'s `classifier_paper_uncond_nocap24H` with `hq_proved`.
* `uncond_nocap24_eq_172`, `uncond_nocap24_eq_179`: `rfl` checks.
-/

namespace BstLean.Part180

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n ≥ 24 000` (no upper end) and every
threshold `t`.** -/
theorem classifier_paper_uncond_nocap24 {n : ℕ} (hn : 24000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_nocap24H hq_proved hn t

theorem uncond_nocap24_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_nocap24 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_nocap24_eq_179 {n : ℕ} (hn : 25000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_nocap24 (by omega) t =
      BstLean.Part179.classifier_paper_uncond_nocap25 hn t :=
  rfl

end BstLean.Part180
