import BstLean.Part153Bin
import BstLean.Part130Layer

/-! The first-layer activation supplies the radial factor in the third statistic. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part153

theorem activation_moment256 {n m : ℕ} {x : Fin n → ℝ}
    (hx : normSq x ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∫⁻ A : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (normSq (reluV (A *ᵥ x)) ^ 128) ∂gaussMat m n γ ≤
      ENNReal.ofReal ((γ * (sqrt ((m : ℝ) / 2) + gaussMomConst 128) ^ 2) ^ 128) := by
  let C := sqrt ((m : ℝ) / 2) + gaussMomConst 128
  have hC : 0 ≤ C := add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _)
  have hf : Measurable (fun z : Fin m → ℝ =>
      ENNReal.ofReal (normSq (reluV z) ^ 128)) :=
    (measurable_normSq.comp continuous_reluV.measurable).pow_const 128 |>.ennreal_ofReal
  rw [← lintegral_map hf (measurable_mulVec_right x), gaussMat_mulVec,
    lintegral_map hf (measurable_const_smul _)]
  have hc : 0 ≤ sqrt γ * sqrt (normSq x) := by positivity
  have he (z : Fin m → ℝ) : normSq (reluV ((sqrt γ * sqrt (normSq x)) • z)) ^ 128 =
      ((sqrt γ * sqrt (normSq x)) ^ 2) ^ 128 * normSq (reluV z) ^ 128 := by
    rw [reluV_smul_of_nonneg hc, normSq_smul, mul_pow]
  simp_rw [he,
    ENNReal.ofReal_mul (pow_nonneg (sq_nonneg _) 128)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : ∫⁻ z : Fin m → ℝ, ENNReal.ofReal (normSq (reluV z) ^ 128)
      ∂stdGauss (Fin m) ≤ ENNReal.ofReal (C ^ 256) := by
    have h := nrm_reluV_moment_lintegral m (by norm_num : 1 ≤ 128)
    have hnrm (z : Fin m → ℝ) : nrm (reluV z) ^ (2 * 128) =
        normSq (reluV z) ^ 128 := by
      rw [pow_mul, nrm, sq_sqrt (normSq_nonneg _)]
    simp_rw [hnrm] at h
    exact h
  refine (mul_le_mul' le_rfl hm).trans ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg (sq_nonneg _) 128)]
  apply ENNReal.ofReal_le_ofReal
  have hs : (sqrt γ * sqrt (normSq x)) ^ 2 ≤ γ := by
    rw [mul_pow, sq_sqrt hγ, sq_sqrt (normSq_nonneg _)]
    nlinarith
  calc
    ((sqrt γ * sqrt (normSq x)) ^ 2) ^ 128 * C ^ 256 =
        ((sqrt γ * sqrt (normSq x)) ^ 2 * C ^ 2) ^ 128 := by
      rw [mul_pow ((sqrt γ * sqrt (normSq x)) ^ 2) (C ^ 2) 128,
        ← pow_mul C 2 128]
    _ ≤ (γ * C ^ 2) ^ 128 :=
      pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) 128

#print axioms activation_moment256
end BstLean.Part223
