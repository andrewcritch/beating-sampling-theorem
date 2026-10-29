import BstLean.Part223CompleteCharge

/-! A coarse order-sixteen plane-radius polynomial enclosure avoids a large
Gamma certificate when only a bias-payment allowance is needed. -/
namespace BstLean.Part252
open MeasureTheory Real
open BstLean.Part29 (gaussMom)
open BstLean.Part186.RA
open BstLean.Part213 BstLean.Part223

theorem radius_square_moment_price :
    (∫ p, RR p ^ 16 ∂ρ2) ≤ (32 : ℝ) ^ 16 / 2 ^ 15 - 1 := by
  have he : (∫ p, RR p ^ 16 ∂ρ2) = ∫ p, planeRadius p ^ 32 ∂ρ2 := by
    congr 1
    funext p
    rw [show (32 : ℕ) = 2 * 16 from rfl, pow_mul, planeRadius_sq]
  rw [he, planeRadius_gamma]
  norm_num only
  have hg := Gamma_nat_eq_factorial 16
  norm_num only [Nat.cast_ofNat] at hg
  rw [hg]
  norm_num [rpow_neg, rpow_natCast, Nat.factorial]

theorem radius_polynomial_root_price {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    radiusPolynomialRoot16 a b c ≤ 32 * (a + b + c) := by
  let K := a + b + c
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (p : ℝ × ℝ) :
      radiusPolynomial a b c p ^ 16 ≤ K ^ 16 * 2 ^ 15 * (1 + RR p ^ 16) := by
    have hr : 0 ≤ planeRadius p := sqrt_nonneg _
    have hr2 := planeRadius_sq p
    have hR := RR_nonneg p
    have hrad : planeRadius p ≤ 1 + RR p := by nlinarith
    have hpoly : radiusPolynomial a b c p ≤ K * (1 + RR p) := by
      unfold radiusPolynomial
      dsimp [K]
      nlinarith [mul_nonneg hb (sub_nonneg.mpr hrad), mul_nonneg ha hR]
    have hp0 : 0 ≤ radiusPolynomial a b c p := by
      unfold radiusPolynomial
      positivity
    have hp := pow_le_pow_left₀ hp0 hpoly 16
    rw [mul_pow] at hp
    have ht := two_point (by norm_num : (0 : ℝ) ≤ 1) hR
      (by norm_num : (0 : ℝ) < 1) 15
    norm_num only at ht
    have ht' : (1 + RR p) ^ 16 ≤ 2 ^ 15 * (1 + RR p ^ 16) := by
      convert ht using 1 <;> ring
    exact hp.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht' (pow_nonneg hK 16))
  apply le_of_pow_le_pow_left₀ (by norm_num : (16 : ℕ) ≠ 0) (by positivity)
  rw [radiusPolynomialRoot16_pow]
  have hi := ((integrable_const (1 : ℝ)).add (int_RR_pow 16).1).const_mul
    (K ^ 16 * 2 ^ 15)
  calc
    _ ≤ ∫ p, K ^ 16 * 2 ^ 15 * (1 + RR p ^ 16) ∂ρ2 :=
      integral_mono (radius_polynomial_power a b c 16).1 hi hpoint
    _ = K ^ 16 * 2 ^ 15 * (1 + ∫ p, RR p ^ 16 ∂ρ2) := by
      rw [integral_const_mul, integral_add (integrable_const _) (int_RR_pow 16).1]
      simp
    _ ≤ K ^ 16 * 2 ^ 15 * (1 + ((32 : ℝ) ^ 16 / 2 ^ 15 - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith [radius_square_moment_price]) (by positivity)
    _ = (32 * (a + b + c)) ^ 16 := by
      change K ^ 16 * 2 ^ 15 * (1 + ((32 : ℝ) ^ 16 / 2 ^ 15 - 1)) = (32 * K) ^ 16
      rw [mul_assoc, show (2 : ℝ) ^ 15 * (1 + (32 ^ 16 / 2 ^ 15 - 1)) = 32 ^ 16 by norm_num]
      rw [mul_pow, mul_comm]

end BstLean.Part252
