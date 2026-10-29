import BstLean.Part264PilotCentreTerms
namespace BstLean.Part264b
open Real BstLean.Part153 BstLean.Part154 BstLean.Part253
theorem piBar_upper_of_bounds {ρ : ℝ} (hlo : 0 < ρ) (hhi : ρ ≤ 0.00026185) : piBar (ρ) ≤ (1 / 10 ^ 40 : ℝ) := by
  have hrlo := hlo
  have hrhi := hhi
  have hs : (0.9997381 : ℝ) ≤ √(1 - 2 * ρ) :=
    le_sqrt_of_sq_le (by linarith)
  have h2 : (1.414213562 : ℝ) ≤ √2 := le_sqrt_of_sq_le (by norm_num)
  have hi : (1 : ℝ) / √2 ≤ 0.707106782 := by
    calc
      _ ≤ (1 : ℝ) / 1.414213562 := by gcongr
      _ ≤ (0.707106782 : ℝ) := by norm_num
  have hgap : (0.292631318 : ℝ) ≤ √(1 - 2 * ρ) - 1 / √2 := by linarith
  have hexp : (100 : ℝ) ≤ (√(1 - 2 * ρ) - 1 / √2) ^ 2 /
      (2 * ρ) := by
    apply (le_div_iff₀ (by linarith : 0 < 2 * ρ)).mpr
    nlinarith
  have h := exp_negative_bound 100 (by norm_num : ((2.71828 : ℝ) ^ 100)⁻¹ ≤ 1 / 10 ^ 40)
  unfold piBar
  apply le_trans ?_ h
  apply exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  linarith


end BstLean.Part264b
