import BstLean.Part143HidC2
import BstLean.Part187R143HidC

/-! Part 187 (file `Part187R143HidC2`): copy of `Part143HidC2` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part143.R

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part140 hiding dotp_self


section row

variable {k : ℕ}

end row

variable {N m : ℕ}

/-- The constant of `goodHatExtra143s` at the floor `16250` (Part 143: `14.04`). -/
noncomputable def cExtra187 : ℝ := 1416 / 100


/-- **The two events of the computed centre, sharper**, `n ≥ 16250`:
`Pr(goodDist n (3/4) fails) + Pr(goodT n (1/400000) fails) ≤ 14.16/n`. -/
theorem goodHatExtra143s {n : ℕ} (hn : 16250 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
      (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ ≤ cExtra187 / (n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hρ := nsq_div_mW_le128 hn
  have h2 := goodDist_prob143s hn4 (Xc := 3 / 4) (by norm_num)
  have h3 := goodT_prob143 hn4 (dT := 1 / 400000) (by norm_num)
  have e1 : (1 : ℝ) / (127 * (n : ℝ)) = 1 / 127 / (n : ℝ) := by field_simp
  rw [e1] at hρ
  have b2 : 31176 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (3 / 4 - 8 / 25) ^ 2 ≤
      1329 / 100 / (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 31176 / 100)
    refine this.trans ?_
    have e4 : (31176 : ℝ) / 100 * (1 / 127 / (n : ℝ)) = 31176 / 100 / 127 / (n : ℝ) := by ring
    have e5 : (1329 : ℝ) / 100 / (n : ℝ) * (3 / 4 - 8 / 25) ^ 2 =
        1329 / 100 * (3 / 4 - 8 / 25) ^ 2 / (n : ℝ) := by ring
    rw [e4, e5]
    refine div_le_div_of_nonneg_right ?_ hnpos.le
    norm_num
  have b3 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * (1 / 400000)) ≤
      87 / 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4465 / 1000)
    have h5 : 4465 / 1000 * ((n : ℝ) ^ 2 / (mW n : ℝ)) * (n : ℝ) ≤ 4465 / 1000 * (1 / 127) := by
      have := mul_le_mul_of_nonneg_right this hnpos.le
      refine this.trans (le_of_eq ?_)
      field_simp
    refine h5.trans ?_
    nlinarith
  unfold cExtra187
  have e3 : (1416 : ℝ) / 100 / (n : ℝ) = 1329 / 100 / (n : ℝ) + 87 / 100 / (n : ℝ) := by ring
  rw [e3]
  exact add_le_add (h2.trans b2) (h3.trans b3)

/-- **The good hidden event for the computed centre, sharper**, `n ≥ 16250`:
`Pr(goodHat n fails) ≤ P143 + cExtra187/n = 0.000775 + 14.16/n`. -/
theorem goodHat_compl143s {n : ℕ} (hn : 16250 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ P143 + cExtra187 / (n : ℝ) := by
  have h1 := good136_prob143 (n := n) (by omega)
  have h23 := goodHatExtra143s hn
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end BstLean.Part143.R

