import BstLean.Part183EnJ
import BstLean.Part183CEnd
import BstLean.Part183KEnd
import BstLean.Part183FComb
import BstLean.Part183GComb
import BstLean.Part183TI
import BstLean.Part183UI
import BstLean.Part182Uncond
import BstLean.Part180HQS

/-!
# Part 183 (file `Uncond`): the classifier theorem with NO hypothesis for every `n ≥ 19 000`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_19000`**: every `n ≥ 19 000`, every threshold `t`, no upper end.
  Ranges: `19 000 ≤ n < 20 000`: chain `classifier_paper_uncond_19000HJ` with Lemma HQ, the frame
  junction `FREE19_of_TI (TI_lite_19000)` and `EnJ_proved`; `20 000 ≤ n < 21 500`: chain
  `classifier_paper_uncond_20000HJ` with `FREE20_of_TI (TI_lite_20000)`; `n ≥ 21 500`: Part 182's
  `classifier_paper_uncond_21500` (which keeps Part 174's cap removal).
* `uncond_19000_eq_172`, `uncond_19000_eq_182`: the same proposition as Parts 172 and 182 (`rfl`).
-/

namespace BstLean.Part183

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_19000 {n : ℕ} (hn : 19000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 20000
  · have hTI : ∀ m : ℕ, 19000 ≤ m →
        BstLean.Part182.TI_hyp m (374 / 1000) (650 / 1000) (735 / 1000) (1 / 10 ^ 18) :=
      fun m hm => BstLean.Part182.TI_hyp_mono (by norm_num) le_rfl (TI_lite_19000 hm)
    exact classifier_paper_uncond_19000HJ (n₁ := 19000) ⟨BstLean.Part180.hq_proved, FREE19_of_TI hTI⟩
      EnJ_proved le_rfl hn (by exact_mod_cast h1.le) t
  · by_cases h2 : n < 21500
    · exact classifier_paper_uncond_20000HJ (n₁ := 20000)
        ⟨BstLean.Part180.hq_proved, FREE20_of_TI fun m hm => TI_lite_20000 hm⟩
        EnJ_proved le_rfl (by omega) (by exact_mod_cast h2.le) t
    · exact BstLean.Part182.classifier_paper_uncond_21500 (by omega) t

theorem uncond_19000_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_19000 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_19000_eq_182 {n : ℕ} (hn : 21500 ≤ n) (t : ℝ) :
    classifier_paper_uncond_19000 (by omega) t =
      BstLean.Part182.classifier_paper_uncond_21500 hn t :=
  rfl

end BstLean.Part183

#print axioms BstLean.Part183.classifier_paper_uncond_19000
#print axioms BstLean.Part183.uncond_19000_eq_172
