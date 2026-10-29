import BstLean.Part293LowNormalization

/-! The actual high-order mixture scalar is the normalized envelope scalar. -/
namespace BstLean.Part293
open Real BstLean.Part293.Model BstLean.Part162 BstLean.Part195 BstLean.Part242

theorem lowIFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureI n 4 = Envelope.iota4 (1 / n) := by
  rw [lowMixtureI, lowWidth_normalized hn, Envelope.iota4_formula]
  norm_num [iotaP] <;> ring

theorem lowISix_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureI n 6 = Envelope.iota6 (1 / n) := by
  rw [lowMixtureI, lowWidth_normalized hn, Envelope.iota6_formula]
  norm_num [iotaP] <;> ring

theorem lowEFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureE n 4 = Envelope.ecoef4 (1 / n) * lowLatitudeT n 4 := by
  rw [lowMixtureE, lowWidth_normalized hn, lowIFour_normalized hn, Envelope.ecoef4_formula]
  norm_num <;> ring <;> simp

theorem lowESix_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureE n 6 = Envelope.ecoef6 (1 / n) * lowLatitudeT n 6 := by
  rw [lowMixtureE, lowWidth_normalized hn, lowISix_normalized hn, Envelope.ecoef6_formula]
  norm_num <;> ring <;> simp

theorem lowLocationFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureLocation n 4 = √(n : ℝ) * Envelope.dcoef4 (1 / n) * lowLatitudeT n 4 := by
  rw [lowMixtureLocation, lowChi_normalized, lowIFour_normalized hn, Envelope.dcoef4_formula,
    show (n : ℝ) * Envelope.chi (1 / n) / 0.18 = n * (Envelope.chi (1 / n) / 0.18) by ring,
    sqrt_mul (Nat.cast_nonneg n)]
  norm_num <;> ring <;> simp

theorem lowLocationSix_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureLocation n 6 = √(n : ℝ) * Envelope.dcoef6 (1 / n) * lowLatitudeT n 6 := by
  rw [lowMixtureLocation, lowChi_normalized, lowISix_normalized hn, Envelope.dcoef6_formula,
    show (n : ℝ) * Envelope.chi (1 / n) / 0.18 = n * (Envelope.chi (1 / n) / 0.18) by ring,
    sqrt_mul (Nat.cast_nonneg n)]
  norm_num <;> ring <;> simp

theorem lowTFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureT n 4 = Envelope.T4 (1 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lowMixtureT, lowK_normalized hn, lowL_normalized hn, lowEFour_normalized hn,
    lowLocationFour_normalized hn, normalized_tK hn0,
    lowLatitude_square_normalized hn (by norm_num), Envelope.T4_formula, Envelope.ntau4_formula]
  norm_num <;> simp only [div_eq_mul_inv, one_div] <;> ring

theorem lowTSix_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureT n 6 = Envelope.T6 (1 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [lowMixtureT, lowK_normalized hn, lowL_normalized hn, lowESix_normalized hn,
    lowLocationSix_normalized hn, normalized_tK hn0,
    lowLatitude_square_normalized hn (by norm_num), Envelope.T6_formula, Envelope.ntau6_formula]
  norm_num <;> simp only [div_eq_mul_inv, one_div] <;> ring

theorem lowEpsilonSquare_normalized {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ) * lowMixtureEpsilon n ^ 2 = Envelope.n_eps2 (1 / n) := by
  rw [lowMixtureEpsilon, eps0, epsilon_square_scaled (by norm_num)]
  have hw : (n : ℝ) * lowMixtureWidth n ^ 2 =
      (49 / 4 : ℝ) * ((n : ℝ) * lowLatitudeT n 12 ^ 2) := by
    unfold lowMixtureWidth
    norm_num <;> ring <;> simp
  rw [hw, lowLatitude_square_normalized hn (by norm_num), lowWidth_normalized hn,
    Envelope.n_eps2_formula]
  simp only [div_mul_eq_div_div]
  norm_num <;> ring <;> simp

theorem lowQ_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureQ n = Envelope.chi2 (1 / n) := by
  have hA : (n : ℝ) * lowMixtureA n ^ 2 = Envelope.An (1 / n) * Envelope.A (1 / n) := by
    rw [show (n : ℝ) * lowMixtureA n ^ 2 = ((n : ℝ) * lowMixtureA n) * lowMixtureA n by ring,
      lowAn_normalized hn, lowA_normalized hn]
  have hcap : lowMixtureK n * ((n : ℝ) * lowMixtureEpsilon n ^ 2 / 2 +
      lowMixtureL n * (1 + lowMixtureEpsilon n)) = Envelope.cap (1 / n) := by
    rw [lowK_normalized hn, lowEpsilonSquare_normalized hn, lowL_normalized hn,
      lowEpsilon_normalized hn, Envelope.cap_formula]
    ring
  rw [lowMixtureQ, hA, hcap,
    lowK_normalized hn, lowT2_normalized hn, lowTFour_normalized hn, lowTSix_normalized hn,
    lowEpsilon_normalized hn, lowA_normalized hn, lowD_normalized hn,
    Envelope.chi2_formula]
  ring

end BstLean.Part293
