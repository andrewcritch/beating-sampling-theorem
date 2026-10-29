import BstLean.Part254GaussianData
import BstLean.Part254GaussianJoint
import BstLean.Part254Scalar

namespace BstLean.Part254
open Real Set BstLean.Part199 BstLean.Part238 BstLean.Part251

theorem gaussian_core_pair_upper :
    gaussianPair exampleCore ≤ (1374279 / 10 ^ 9 : ℝ) := gaussianTail_32.2

theorem gaussian_core_outside_upper :
    gaussianOutside exampleCore ≤ (6216465741 / 10 ^ 12 : ℝ) := by
  have h : exp (-(9375 / 10000 : ℝ)) ≤ 391605626677 / 10 ^ 12 := by
    apply BstLean.Part156.exp_le_taylor (b := 1) 20 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have hp := pow_le_pow_left₀ (exp_nonneg _) h 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  change gaussianTail (28 / 10) + 2 * exp (-(75 / 10 : ℝ)) ≤ _
  rw [show -(75 / 10 : ℝ) = -(15 / 2) by norm_num]
  exact (add_le_add gaussianTail_28.2
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2))).trans (by norm_num)

theorem gaussian_wide_outside_upper :
    gaussianOutside exampleWide ≤ (6095484 / 10 ^ 15 : ℝ) := by
  have h := BstLean.Part182.exp_neg_nat_le 20
  norm_num at h
  change gaussianTail 6 + 2 * exp (-20 : ℝ) ≤ _
  exact (add_le_add gaussianTail_6.2
    (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2))).trans (by norm_num)

theorem gaussian_exceptional_upper {b : ℝ} (hb : b ≤ 28 / 10 ^ 16) :
    2 * √(√(gaussianTail exampleWide.pair + 2 * b)) + √(gaussianOutside exampleWide) ≤
      (65333 / 10 ^ 8 : ℝ) := by
  have hp : gaussianTail exampleWide.pair ≤ (1244193 / 10 ^ 21 : ℝ) := gaussianTail_8.2
  have hq : √(√(gaussianTail exampleWide.pair + 2 * b)) ≤ (287628 / 10 ^ 9 : ℝ) := by
    apply BstLean.Part182.sqrt_sqrt_le_of (by norm_num)
    linarith only [hp, hb]
  have ho : √(gaussianOutside exampleWide) ≤ (78074 / 10 ^ 9 : ℝ) := by
    apply BstLean.Part182.sqrt_le_of_sq' (by norm_num)
    linarith only [gaussian_wide_outside_upper]
  linarith only [hq, ho]

noncomputable def fixedGaussianCovariance (n : ℕ) (θ : ℝ) : ℝ :=
  gaussianScalar n θ exampleWide exampleCore fixedCore (67 / 100)
    (1 - 4 * θ / n)⁻¹ (13 / 10)
    (gaussianTail exampleWide.pair + 2 * (BstLean.Part249.optionBDelta n / (1 / 4000)))

noncomputable def gaussianEnvelope (θ : ℝ) : ℝ :=
  θ * ((598514915 / 10 ^ 9) / (1 - 4 * θ / 12225) +
    (67 / 100) / (1 - radiusEnvelope θ false) * (1374279 / 10 ^ 9) +
    (67 / 100) / (1 - radiusEnvelope θ true) * (6216465741 / 10 ^ 12)) +
    (13 / 10) * (65333 / 10 ^ 8)

theorem gaussianScalar_mono_K {n : ℕ} {θ : ℝ} {w₀ w₁ : Window} {K K' lam E M h : ℝ}
    (hθ : 0 ≤ θ) (hE : 0 ≤ E) (hK : K ≤ K') :
    gaussianScalar n θ w₀ w₁ K lam E M h ≤ gaussianScalar n θ w₀ w₁ K' lam E M h := by
  unfold gaussianScalar
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK hE) hθ
  linarith

end BstLean.Part254
