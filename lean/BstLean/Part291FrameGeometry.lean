import BstLean.Part291RadiusWeights
import BstLean.Part291Windows
import BstLean.Part235Covariance

namespace BstLean.BlueprintLow
open Real BstLean.Part208 BstLean.Part153

/-- The core radial denominator is positive for every centre length. -/
theorem lowCoreRadius_positive {n : ℕ} (hn : 8000 ≤ n) (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < axialRadiusLower n a τ lowCoreWindow.t lowCoreWindow.z := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : √((n : ℝ) * 7.81) ≤ 0.032 * n := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith
  have hg : 0 < (n : ℝ) - 2 * √((n : ℝ) * 7.81) - 2.88 ^ 2 := by linarith
  have h := mul_pos (sq_pos_of_pos hτ) hg
  unfold axialRadiusLower
  change 0 < a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * 7.81)) - 2 * a * τ * 2.88
  nlinarith [sq_nonneg (a - τ * 2.88)]

end BstLean.BlueprintLow
