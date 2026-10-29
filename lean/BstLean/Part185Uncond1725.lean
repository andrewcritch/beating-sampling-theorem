import BstLean.Part185CEnd
import BstLean.Part185FUI
import BstLean.Part184Uncond175

/-!
# Part 185 (file `Uncond1725`): the classifier theorem with NO hypothesis for every `n ≥ 17 250`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_17250`**: every `n ≥ 17 250`, every threshold `t`, no upper end.
  Ranges: `17 250 ≤ n ≤ 17 500`: the chain `classifier_paper_uncond_17250HB` (files `C*`, removal
  tolerance `η = 1/250`, floor `sd = 0.4482`, room `−0.00265`) with Lemma HQ, the frame junction
  `FREE1725_proved` (files `F*`, room `−0.002503`, weakened by `FREEg_mono`), `EnB_proved`,
  `EnFB_proved`; `n > 17 500`: Part 184's `classifier_paper_uncond_17500`.
* `uncond_17250_eq_172`, `uncond_17250_eq_184`: the same proposition (`rfl`).
-/

namespace BstLean.Part185

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_17250 {n : ℕ} (hn : 17250 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n ≤ 17500
  · exact classifier_paper_uncond_17250HB ⟨BstLean.Part180.hq_proved,
      BstLean.Part183.FREEg_mono le_rfl (by norm_num) FREE1725_proved⟩
      BstLean.Part184.EnB_proved BstLean.Part184.EnFB_proved hn h1 t
  · exact BstLean.Part184.classifier_paper_uncond_17500 (by omega) t

theorem uncond_17250_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_17250 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_17250_eq_184 {n : ℕ} (hn : 17500 ≤ n) (t : ℝ) :
    classifier_paper_uncond_17250 (by omega) t = BstLean.Part184.classifier_paper_uncond_17500 hn t :=
  rfl

end BstLean.Part185

#print axioms BstLean.Part185.classifier_paper_uncond_17250
