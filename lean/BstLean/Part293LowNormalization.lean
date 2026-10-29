import BstLean.Part293LowModel
import BstLean.Part293Envelope
import BstLean.Part293Normalize
import BstLean.Part293MixtureAlgebra

/-! Exact identities between the isolated scalar model and the common envelope. -/
namespace BstLean.Part293
open Real BstLean.Part293.Model BstLean.Part162 BstLean.Part195 BstLean.Part242 BstLean.Part248

noncomputable def normalizedLatitude (x : ℝ) (q : ℕ) : ℝ :=
  rotationConstant q * √(1521 / 500 : ℝ) * x / √(1 - x * (1 + 2 * q))

theorem lowLatitude_normalized {n q : ℕ} (hn : 8000 ≤ n) (hq : q ≤ 12) :
    lowLatitudeT n q = normalizedLatitude (1 / n) q := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  unfold lowLatitudeT normalizedLatitude
  rw [show (n : ℝ) - 1 - 2 * q = n - (1 + 2 * q) by ring,
    latitude_normalization (by linarith) (by linarith) (by norm_num),
    show (3.042 : ℝ) = 1521 / 500 by norm_num,
    show 1 - (1 + 2 * (q : ℝ)) * (1 / n) = 1 - (1 / n) * (1 + 2 * q) by ring]
  ring

theorem lowMean_normalized (n : ℕ) : lowMixtureMean n = Envelope.mu (1 / n) := by
  rw [lowMixtureMean, Envelope.mu_formula]
  congr 1 <;> congr 1 <;> norm_num [agentEnergyCap, agentParallelCap] <;> ring

theorem lowY_normalized (n : ℕ) : lowMixtureY n = Envelope.Y0 (1 / n) := by
  rw [lowMixtureY, lowMean_normalized, Envelope.Y0_formula]

theorem lowH_normalized (n : ℕ) : agentEnergyMomentCap / n = Envelope.H (1 / n) := by
  rw [Envelope.H_formula]
  norm_num [agentEnergyMomentCap] <;> ring

theorem lowV_normalized {n : ℕ} (hn : 8000 ≤ n) : lowLatitudeV n = Envelope.V (1 / n) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [lowLatitudeV, variance_normalization (by linarith) (by linarith), Envelope.V_formula]
  norm_num <;> ring

theorem lowChi_normalized (n : ℕ) : lowMixtureChi n = Envelope.chi (1 / n) := by
  rw [lowMixtureChi, Envelope.chi_formula]
  rw [show (12 : ℝ) / n = (1 / n) * 12 by ring]
  ring

theorem lowTwelve_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowLatitudeT n 12 = Envelope.tau12 (1 / n) := by
  rw [lowLatitude_normalized hn (by norm_num), Envelope.tau12_formula]
  norm_num [normalizedLatitude]

theorem lowFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowLatitudeT n 4 = Envelope.tau4 (1 / n) := by
  rw [lowLatitude_normalized hn (by norm_num), Envelope.tau4_formula]
  norm_num [normalizedLatitude]

theorem lowEight_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowLatitudeT n 8 = Envelope.tau8 (1 / n) := by
  rw [lowLatitude_normalized hn (by norm_num), Envelope.tau8_formula]
  norm_num [normalizedLatitude]

theorem lowWidth_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureWidth n = Envelope.dw (1 / n) := by
  rw [lowMixtureWidth, lowTwelve_normalized hn, Envelope.tau12_formula, Envelope.dw_formula]
  norm_num <;> ring

theorem lowEpsilon_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureEpsilon n = Envelope.eps (1 / n) := by
  rw [lowMixtureEpsilon, lowWidth_normalized hn, eps0, Envelope.eps_formula]
  norm_num <;> ring

theorem lowX_normalized (n q : ℕ) :
    lowMixtureX n q = 2 * Envelope.H (1 / n) +
      2 * Envelope.mu (1 / n) * rotationConstant (q / 2) *
        √((1 / n) * (27323 / 250000 : ℝ)) +
      rotationConstant q ^ 2 * (27323 / 250000 : ℝ) * (1 / n) := by
  rw [lowMixtureX, deficitConstant, lowH_normalized, lowMean_normalized]
  rw [show agentDirectionCap / (n : ℝ) = (1 / n) * (27323 / 250000 : ℝ) by
    norm_num [agentDirectionCap] <;> ring]
  rw [mul_pow, sq_sqrt (by positivity)]
  ring

theorem lowXFour_normalized (n : ℕ) : lowMixtureX n 4 = Envelope.X4 (1 / n) := by
  rw [lowX_normalized, Envelope.X4_formula]
  norm_num <;> ring

theorem lowXEight_normalized (n : ℕ) : lowMixtureX n 8 = Envelope.X8 (1 / n) := by
  rw [lowX_normalized, Envelope.X8_formula]
  norm_num <;> ring

theorem lowXTwelve_normalized (n : ℕ) : lowMixtureX n 12 = Envelope.X12 (1 / n) := by
  rw [lowX_normalized, Envelope.X12_formula]
  norm_num <;> ring

theorem lowXhatFour_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureXhat n 4 = Envelope.Xhat4 (1 / n) := by
  rw [lowMixtureXhat, mixtureConstant, lowX_normalized, lowH_normalized,
    lowFour_normalized hn, lowV_normalized hn, Envelope.Xhat4_formula]
  norm_num <;> ring

theorem lowXhatEight_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureXhat n 8 = Envelope.Xhat8 (1 / n) := by
  rw [lowMixtureXhat, mixtureConstant, lowX_normalized, lowH_normalized,
    lowEight_normalized hn, lowV_normalized hn, Envelope.Xhat8_formula]
  norm_num <;> ring

theorem lowXhatTwelve_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureXhat n 12 = Envelope.Xhat12 (1 / n) := by
  rw [lowMixtureXhat, mixtureConstant, lowX_normalized, lowH_normalized,
    lowTwelve_normalized hn, lowV_normalized hn, Envelope.Xhat12_formula]
  norm_num <;> ring

theorem lowReciprocal_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureReciprocal n = Envelope.G (1 / n) := by
  rw [lowMixtureReciprocal, lowY_normalized, lowXhatFour_normalized hn,
    lowXhatEight_normalized hn, lowXhatTwelve_normalized hn, bound3, Envelope.G_formula]
  norm_num <;> ring

theorem lowBiasReciprocal_normalized (n : ℕ) :
    bound3 0.17919 (lowMixtureY n) (lowMixtureX n 4) (lowMixtureX n 8)
      (lowMixtureX n 12) = Envelope.Gamma (1 / n) := by
  rw [lowY_normalized, lowXFour_normalized, lowXEight_normalized,
    lowXTwelve_normalized, bound3, Envelope.Gamma_formula]
  norm_num <;> ring

theorem lowA_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureA n = Envelope.A (1 / n) := by
  rw [lowMixtureA, mixA, lowWidth_normalized hn, lowReciprocal_normalized hn,
    lowV_normalized hn, Envelope.A_formula, Envelope.factor_formula]
  norm_num <;> ring

theorem lowD_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureD n (lowMixtureChi n) = Envelope.D (1 / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [lowMixtureD, mixD, lowChi_normalized, lowReciprocal_normalized hn,
    lowV_normalized hn, Envelope.V_formula, Envelope.D_formula]
  norm_num
  field_simp <;> ring

theorem lowB_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureB n = Envelope.B (1 / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hcancel (r : ℝ) : (n : ℝ) * r / n = r := by field_simp
  have hD : agentDirectionCap / (n : ℝ) = (1 / n) * (27323 / 250000 : ℝ) := by
    norm_num [agentDirectionCap] <;> ring
  have hxi : agentParallelCap / (n : ℝ) = (1 / n) * (26927 / 500000 : ℝ) := by
    norm_num [agentParallelCap] <;> ring
  have hgap : √((1 - (0.0066 : ℝ)) ^ 2 - 0.18) -
      (√agentEnergyCap + √(agentParallelCap / n)) = Envelope.gap (1 / n) := by
    rw [hxi, Envelope.gap_formula]
    norm_num [agentEnergyCap] <;> ring
  have hs : √((1 / (n : ℝ)) * (27323 / 250000 : ℝ)) ^ 24 =
      ((1 / (n : ℝ)) * (27323 / 250000 : ℝ)) ^ 12 := by
    rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, sq_sqrt (by positivity)]
  rw [lowMixtureB, lowMixtureBeta, BstLean.Part222.massBound,
    hcancel, lowH_normalized, hD, hgap, Envelope.B_formula]
  simp only [div_pow, mul_pow, hs]
  norm_num <;> ring

theorem lowLatitude_square_normalized {n q : ℕ} (hn : 8000 ≤ n) (hq : q ≤ 12) :
    (n : ℝ) * lowLatitudeT n q ^ 2 =
      rotationConstant q ^ 2 * (1521 / 500 : ℝ) * (1 / n) /
        (1 - (1 + 2 * (q : ℝ)) * (1 / n)) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  rw [lowLatitudeT, show (n : ℝ) - 1 - 2 * q = n - (1 + 2 * q) by ring,
    show (3.042 : ℝ) = 1521 / 500 by norm_num]
  exact normalized_latitude_square (by linarith) (by linarith) (by norm_num)

theorem lowL_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureL n = Envelope.L (1 / n) := by
  rw [lowMixtureL, lowMixtureWidth, lowChi_normalized]
  calc
    _ = Envelope.chi (1 / n) * 49 / 0.18 * ((n : ℝ) * lowLatitudeT n 12 ^ 2) := by
      norm_num <;> ring
    _ = _ := by
      rw [lowLatitude_square_normalized hn (by norm_num), Envelope.L_formula]
      norm_num <;> ring

theorem lowK_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureK n = Envelope.kap (1 / n) := by
  simp only [lowMixtureK, lowEpsilon_normalized hn, Envelope.kap_formula, one_div]

theorem lowAn_normalized {n : ℕ} (hn : 8000 ≤ n) :
    (n : ℝ) * lowMixtureA n = Envelope.An (1 / n) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [lowA_normalized hn, Envelope.scaled_energy_identity]
  field_simp

theorem lowT2_normalized {n : ℕ} (hn : 8000 ≤ n) :
    lowMixtureT2 n = Envelope.T2 (1 / n) := by
  rw [lowMixtureT2, lowK_normalized hn, lowAn_normalized hn,
    lowD_normalized hn, lowL_normalized hn, lowA_normalized hn, Envelope.T2_formula]


end BstLean.Part293
