import BstLean.Part293LowNormalization

/-! The displacement identity is isolated from the bias-moment dependency chain. -/
namespace BstLean.Part293
open Real BstLean.Part293.Model BstLean.Part195

theorem lowDisplacement_normalized {n : ℕ} (hn : 8000 ≤ n) :
    √(lowMixtureB n) / (1 - 0.0045) *
      (lowMixtureD n (lowMixtureChi n) / 2 +
        n * (2 * (1 + agentEnergyMomentCap / n) * lowLatitudeT n 4) ^ 2 / (4 * 0.18 ^ 2)) =
      Envelope.Dd (1 / n) := by
  rw [lowB_normalized hn, lowD_normalized hn, lowH_normalized, Envelope.Dd_formula]
  have hs := lowLatitude_square_normalized hn (q := 4) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hs
  have he : (n : ℝ) * (2 * (1 + Envelope.H (1 / n)) * lowLatitudeT n 4) ^ 2 /
      (4 * (0.18 : ℝ) ^ 2) =
      (1 + Envelope.H (1 / n)) ^ 2 / (0.18 : ℝ) ^ 2 *
        ((n : ℝ) * lowLatitudeT n 4 ^ 2) := by ring
  rw [he, hs]
  simp only [div_mul_eq_div_div]
  norm_num <;> ring <;> simp

end BstLean.Part293
