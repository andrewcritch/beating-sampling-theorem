import BstLean.Part184MEnd
import BstLean.Part184IUI
import BstLean.Part184Uncond1775
import BstLean.Part184BF3

/-!
# Part 184 (file `Uncond175`): the classifier theorem with NO hypothesis for every `n ≥ 17 500`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_17500`**: every `n ≥ 17 500`, every threshold `t`, no upper end.
  Ranges: `17 500 ≤ n < 17 750`: the chain `classifier_paper_uncond_17500HB` (files `M*`, room
  `−0.0021`) with Lemma HQ, the frame junction `FREE175_proved` (files `I*`, room `−0.0020`,
  weakened to `−0.0021` by `FREEg_mono`), `EnB_proved`, `EnFB_proved`; `n ≥ 17 750`:
  `classifier_paper_uncond_17750` (file `Uncond1775`).
* `uncond_17500_eq_172`, `uncond_17500_eq_183`, `uncond_17500_eq_17750`: the same proposition (`rfl`).
-/

namespace BstLean.Part184

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_17500 {n : ℕ} (hn : 17500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 17750
  · exact classifier_paper_uncond_17500HB ⟨BstLean.Part180.hq_proved,
      BstLean.Part183.FREEg_mono le_rfl (by norm_num) FREE175_proved⟩
      EnB_proved EnFB_proved hn h1.le t
  · exact classifier_paper_uncond_17750 (by omega) t

theorem uncond_17500_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_17500 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_17500_eq_183 {n : ℕ} (hn : 19000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_17500 (by omega) t =
      BstLean.Part183.classifier_paper_uncond_19000 hn t :=
  rfl

theorem uncond_17500_eq_17750 {n : ℕ} (hn : 17750 ≤ n) (t : ℝ) :
    classifier_paper_uncond_17500 (by omega) t = classifier_paper_uncond_17750 hn t :=
  rfl

end BstLean.Part184

#print axioms BstLean.Part184.classifier_paper_uncond_17500
