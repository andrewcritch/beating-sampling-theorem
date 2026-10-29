import BstLean.Part143HidC2

/-!
# Part 145, file `HidM`: the bad hidden event for `n ≥ 9216`

* `nsq_div_mW_le96`: `n²/mW n ≤ 1/(96 n)` for `n ≥ 9216 = 96²`.
* `goodHatExtra145M`, `goodHat_compl145M`: for `n ≥ 9216`:
  `Pr(goodHat n fails) ≤ 775/1000000 + cExtra145M/n`, `cExtra145M = 19.59`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part140 hiding dotp_self
open BstLean.Part143

/-- `n²/mW n ≤ 1/(96n)` for `n ≥ 9216`. -/
lemma nsq_div_mW_le96 {n : ℕ} (hn : 9216 ≤ n) :
    (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / (96 * (n : ℝ)) := by
  have hn' : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine ratio_le (n0 := n) (by omega) le_rfl (by positivity) ?_
  rw [div_pow, one_pow, mul_pow]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (n : ℝ), mul_pos hnpos hnpos]

/-- The constant of the two events of the computed centre, `n ≥ 9216`. -/
noncomputable def cExtra145M : ℝ := 1959 / 100

/-- **The two events of the computed centre**, `n ≥ 9216`:
`Pr(goodDist n (3/4) fails) + Pr(goodT n (1/400000) fails) ≤ 19.59/n`. -/
theorem goodHatExtra145M {n : ℕ} (hn : 9216 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
      (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ ≤ cExtra145M / (n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (9216 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hρ := nsq_div_mW_le96 hn
  have h2 := goodDist_prob143s hn4 (Xc := 3 / 4) (by norm_num)
  have h3 := goodT_prob143 hn4 (dT := 1 / 400000) (by norm_num)
  have e1 : (1 : ℝ) / (96 * (n : ℝ)) = 1 / 96 / (n : ℝ) := by field_simp
  rw [e1] at hρ
  have b2 : 31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (3 / 4 - 8 / 25) ^ 2 ≤
      1757 / 100 / (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 31176 / 100)
    refine this.trans ?_
    have e4 : (31176 : ℝ) / 100 * (1 / 96 / (n : ℝ)) = 31176 / 100 / 96 / (n : ℝ) := by ring
    have e5 : (1757 : ℝ) / 100 / (n : ℝ) * (3 / 4 - 8 / 25) ^ 2 =
        1757 / 100 * (3 / 4 - 8 / 25) ^ 2 / (n : ℝ) := by ring
    rw [e4, e5]
    refine div_le_div_of_nonneg_right ?_ hnpos.le
    norm_num
  have b3 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * (1 / 400000)) ≤
      202 / 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4465 / 1000)
    have h5 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) * (n : ℝ) ≤ 4465 / 1000 * (1 / 96) := by
      have := mul_le_mul_of_nonneg_right this hnpos.le
      refine this.trans (le_of_eq ?_)
      field_simp
    refine h5.trans ?_
    nlinarith
  unfold cExtra145M
  have e3 : (1959 : ℝ) / 100 / (n : ℝ) = 1757 / 100 / (n : ℝ) + 202 / 100 / (n : ℝ) := by ring
  rw [e3]
  exact add_le_add (h2.trans b2) (h3.trans b3)

/-- **The good hidden event for the computed centre**, `n ≥ 9216`:
`Pr(goodHat n fails) ≤ 0.000775 + 19.59/n`. -/
theorem goodHat_compl145M {n : ℕ} (hn : 9216 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ 775 / 1000000 + cExtra145M / (n : ℝ) := by
  have h1 := good136_prob143 (n := n) (by omega)
  unfold P143 at h1
  have h23 := goodHatExtra145M hn
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms goodHatExtra145M
open BstLean.Part145 in
#print axioms goodHat_compl145M
