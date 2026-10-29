import BstLean.Part292FirstLayer

/-! Activation moments at arbitrary even order and a uniform low-band cap. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152 BstLean.Part153

theorem activation_even_moment {n m j : ℕ} (hj : 1 ≤ j) {x : Fin n → ℝ}
    (hx : normSq x ≤ 1) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∫⁻ A : Matrix (Fin m) (Fin n) ℝ,
      ENNReal.ofReal (normSq (reluV (A *ᵥ x)) ^ j) ∂gaussMat m n γ ≤
      ENNReal.ofReal ((γ * (sqrt ((m : ℝ) / 2) + gaussMomConst j) ^ 2) ^ j) := by
  let C := sqrt ((m : ℝ) / 2) + gaussMomConst j
  have hf : Measurable (fun z : Fin m → ℝ =>
      ENNReal.ofReal (normSq (reluV z) ^ j)) :=
    (BstLean.Part130.measurable_normSq.comp continuous_reluV.measurable).pow_const j |>.ennreal_ofReal
  rw [← lintegral_map hf (measurable_mulVec_right x), gaussMat_mulVec,
    lintegral_map hf (measurable_const_smul _)]
  have hc : 0 ≤ sqrt γ * sqrt (normSq x) := by positivity
  have he (z : Fin m → ℝ) : normSq (reluV ((sqrt γ * sqrt (normSq x)) • z)) ^ j =
      ((sqrt γ * sqrt (normSq x)) ^ 2) ^ j * normSq (reluV z) ^ j := by
    rw [reluV_smul_of_nonneg hc, normSq_smul, mul_pow]
  simp_rw [he, ENNReal.ofReal_mul (pow_nonneg (sq_nonneg _) j)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : ∫⁻ z : Fin m → ℝ, ENNReal.ofReal (normSq (reluV z) ^ j)
      ∂stdGauss (Fin m) ≤ ENNReal.ofReal (C ^ (2 * j)) := by
    have h := nrm_reluV_moment_lintegral m hj
    have hnrm (z : Fin m → ℝ) : nrm (reluV z) ^ (2 * j) = normSq (reluV z) ^ j := by
      rw [pow_mul, nrm, sq_sqrt (normSq_nonneg _)]
    simp_rw [hnrm] at h
    exact h
  refine (mul_le_mul' le_rfl hm).trans ?_
  rw [← ENNReal.ofReal_mul (pow_nonneg (sq_nonneg _) j)]
  apply ENNReal.ofReal_le_ofReal
  have hs : (sqrt γ * sqrt (normSq x)) ^ 2 ≤ γ := by
    rw [mul_pow, sq_sqrt hγ, sq_sqrt (normSq_nonneg _)]
    nlinarith
  calc
    ((sqrt γ * sqrt (normSq x)) ^ 2) ^ j * C ^ (2 * j) =
        ((sqrt γ * sqrt (normSq x)) ^ 2 * C ^ 2) ^ j := by simp only [mul_pow, pow_mul]
    _ ≤ (γ * C ^ 2) ^ j := pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_right hs (sq_nonneg _)) j

theorem activation_constant_band {n : ℕ} (hn : 8000 ≤ n) :
    ((n : ℝ) * BstLean.Part170.tA n / 2) *
      ((2 / (n : ℝ)) * (sqrt ((mA n : ℝ) / 2) + gaussMomConst 832) ^ 2) ≤
      10103 / 10000 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : sqrt ((mA n : ℝ) / 2) = (n : ℝ) / sqrt 2 := by
    rw [mA, Nat.cast_pow, sqrt_div (sq_nonneg _), sqrt_sq (Nat.cast_nonneg _)]
  have hs2 : (14142 / 10000 : ℝ) ≤ sqrt 2 := by
    apply (le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hg := gaussian_moment1664
  have hg0 := gaussMomConst_nonneg 832
  have he : ((n : ℝ) * BstLean.Part170.tA n / 2) *
      ((2 / (n : ℝ)) * (sqrt ((mA n : ℝ) / 2) + gaussMomConst 832) ^ 2) =
      (1 + sqrt 2 * gaussMomConst 832 / n) ^ 2 := by
    rw [hs, BstLean.Part170.tA, mA, Nat.cast_pow]
    field_simp
    nlinarith [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [he]
  have hs2' : sqrt 2 ≤ (14143 / 10000 : ℝ) := by
    apply (sqrt_le_iff).mpr
    norm_num
  have hr : sqrt 2 * gaussMomConst 832 / n ≤ (5127 / 1000000 : ℝ) := by
    apply (div_le_iff₀ hn0).mpr
    have hmul := mul_le_mul hs2' hg hg0 (by norm_num : (0 : ℝ) ≤ 14143 / 10000)
    nlinarith
  have hr0 : 0 ≤ sqrt 2 * gaussMomConst 832 / n := by positivity
  nlinarith

end BstLean.Part292

/-- info: 'BstLean.Part292.activation_even_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.activation_even_moment
