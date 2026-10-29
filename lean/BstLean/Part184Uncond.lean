import BstLean.Part184CEnd
import BstLean.Part184FUI
import BstLean.Part184EnB
import BstLean.Part183Uncond

/-!
# Part 184 (file `Uncond`): the classifier theorem with NO hypothesis for every `n ≥ 18 500`

No proof is left open; no `native_decide` or `axiom` is used.

* **`classifier_paper_uncond_18500`**: every `n ≥ 18 500`, every threshold `t`, no upper end.
  Ranges: `18 500 ≤ n < 19 000`: the chain `classifier_paper_uncond_18500HJ` (files `C*`) with
  Lemma HQ, the frame junction `FREE185_proved` (files `F*`, TI-lite at `18 500`) and the row moment
  expansion `EnB_proved` (files `Mom`, `Row`, `Core`, `EnB`); `n ≥ 19 000`: Part 183's
  `classifier_paper_uncond_19000` (which keeps Part 174's cap removal through Part 182).
* `uncond_18500_eq_172`, `uncond_18500_eq_183`: the same proposition as Parts 172 and 183 (`rfl`).
-/

namespace BstLean.Part184

open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171 BstLean.Part177

theorem classifier_paper_uncond_18500 {n : ℕ} (hn : 18500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  by_cases h1 : n < 19000
  · exact classifier_paper_uncond_18500HJ (n₁ := 18500)
      ⟨BstLean.Part180.hq_proved, FREE185_proved⟩ EnB_proved le_rfl hn (by exact_mod_cast h1.le) t
  · exact BstLean.Part183.classifier_paper_uncond_19000 (by omega) t

theorem uncond_18500_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_18500 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_18500_eq_183 {n : ℕ} (hn : 19000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_18500 (by omega) t =
      BstLean.Part183.classifier_paper_uncond_19000 hn t :=
  rfl

end BstLean.Part184

#print axioms BstLean.Part184.classifier_paper_uncond_18500
#print axioms BstLean.Part184.uncond_18500_eq_172
#print axioms BstLean.Part184.uncond_18500_eq_183
