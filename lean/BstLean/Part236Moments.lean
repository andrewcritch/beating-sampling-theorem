import BstLean.Part227Hidden

namespace BstLean.Part236
open MeasureTheory Real
open BstLean.Part130 BstLean.Part133 BstLean.Part134 BstLean.Part136 BstLean.Part143

noncomputable def markScale (n : ℕ) : ℝ :=
  ((mW n : ℝ) / ((2 * n : ℕ) : ℝ) * cF2o (mW n)) ^ 2

noncomputable def yK {n : ℕ} (θ : HidParam (2 * n) (mW n)) : ℝ := errK θ / markScale n
noncomputable def yD {n : ℕ} (θ : HidParam (2 * n) (mW n)) : ℝ := errD θ / markScale n

lemma markScale_pos {n : ℕ} (hn : 4096 ≤ n) : 0 < markScale n := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hc := BstLean.Part133.cF2o_pos hm
  have hn' : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
  have hm' : (0 : ℝ) < mW n := by exact_mod_cast hm
  unfold markScale
  positivity

lemma yK_nonneg {n : ℕ} (θ : HidParam (2 * n) (mW n)) : 0 ≤ yK θ :=
  div_nonneg (errK_nonneg θ) (sq_nonneg _)
lemma yD_nonneg {n : ℕ} (θ : HidParam (2 * n) (mW n)) : 0 ≤ yD θ :=
  div_nonneg (errD_nonneg θ) (sq_nonneg _)

theorem normalized_moments {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (yK (n := n)) (hidGauss (2 * n) (mW n)) ∧
    Integrable (yD (n := n)) (hidGauss (2 * n) (mW n)) ∧
    (∫ θ, yK θ ∂hidGauss (2 * n) (mW n)) ≤ 372 / 1000 ∧
    (∫ θ, yD θ ∂hidGauss (2 * n) (mW n)) ≤ 448 / 1000 := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hN8 : 8192 ≤ 2 * n := by omega
  have hm' : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hcF : cF2o (mW n) ^ 2 =
      (6 * (1 + 5 / (mW n : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (mW n : ℝ) := by
    unfold cF2o
    rw [Real.sq_sqrt (by positivity)]
    ring
  have h2 : 0 ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 / (mW n : ℝ) := by positivity
  obtain ⟨iK, eK⟩ := errK_mean143 (m := mW n) hN hm
  obtain ⟨iD, eD⟩ := errD_mean143 (m := mW n) hN hm
  have eK' : ∫ θ, errK θ ∂hidGauss (2 * n) (mW n) ≤ 372 / 1000 * markScale n := by
    refine eK.trans ?_
    unfold markScale
    rw [mul_pow, hcF]
    have h := mul_le_mul_of_nonneg_left (cK143_le hN8 hmM) h2
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_)) <;> ring
  have eD' : ∫ θ, errD θ ∂hidGauss (2 * n) (mW n) ≤ 448 / 1000 * markScale n := by
    refine eD.trans ?_
    unfold markScale
    rw [mul_pow, hcF]
    have h := mul_le_mul_of_nonneg_left (cD143_le hmM) h2
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_)) <;> ring
  refine ⟨iK.div_const _, iD.div_const _, ?_, ?_⟩
  · unfold yK
    rw [integral_div]
    exact (div_le_iff₀ (markScale_pos hn)).mpr eK'
  · unfold yD
    rw [integral_div]
    exact (div_le_iff₀ (markScale_pos hn)).mpr eD'

theorem base_error_bounds {n : ℕ} (hn : 4096 ≤ n)
    {θ : HidParam (2 * n) (mW n)}
    (hθ : θ ∈ goodHid (2 * n) (mW n) ((4 / 100) ^ 2) (4 / 10000)) :
    yK θ < 625 ∧ yD θ < 2500 := by
  have hb := markScale_pos hn
  have hk : errK θ < markScale n / ((4 / 100) ^ 2) := hθ.1
  have hd : errD θ < markScale n / (4 / 10000) := hθ.2
  constructor
  · apply (div_lt_iff₀ hb).mpr
    norm_num at hk
    nlinarith
  · apply (div_lt_iff₀ hb).mpr
    norm_num at hd
    nlinarith
end BstLean.Part236
