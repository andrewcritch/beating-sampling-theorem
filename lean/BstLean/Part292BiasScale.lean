import BstLean.Part292BandNumbers
import BstLean.Part292Corrections

/-! The normalized row coefficients cancel the dimension prefactors exactly. -/
namespace BstLean.Part292
open MeasureTheory Real
open BstLean.Part130 BstLean.Part213 BstLean.Part239
open BstLean.Part186.RA (ρ2)

theorem radiusPolynomialRoot104_scale {s : ℝ} (hs : 0 ≤ s) (a b c : ℝ) :
    radiusPolynomialRoot104 (s*a) (s*b) (s*c) = s*radiusPolynomialRoot104 a b c := by
  apply (pow_left_inj₀ (radiusPolynomialRoot104_nonneg _ _ _)
    (mul_nonneg hs (radiusPolynomialRoot104_nonneg _ _ _)) (by norm_num : (104 : ℕ) ≠ 0)).mp
  rw [radiusPolynomialRoot104_pow, mul_pow, radiusPolynomialRoot104_pow]
  have he (p : ℝ × ℝ) : radiusPolynomial (s*a) (s*b) (s*c) p =
      s*radiusPolynomial a b c p := by unfold radiusPolynomial; ring
  simp_rw [he, mul_pow]
  rw [integral_const_mul]

theorem collectedSecond_scale (s a b c : ℝ) :
    collectedSecond (s*a) (s*b) (s*c) = s^2*collectedSecond a b c := by
  unfold collectedSecond
  ring

theorem location_price_normalized {n : ℕ} (hn : 8000 ≤ n) {a b c : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : (n : ℝ)*sqrt n*a ≤ 36/10000)
    (hb : (n : ℝ)*sqrt n*b ≤ 126/100000)
    (hc : (n : ℝ)*sqrt n*c ≤ 41/100000) :
    (n : ℝ)^52*(mA n : ℝ)^52*
      (collectedSecond a b c+exactCorrection 52 (mA n)*radiusPolynomialRoot104 a b c^2)^52 ≤
      (635/100000 : ℝ)^104 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 ≤ (n : ℝ)*sqrt n := by positivity
  have hr : exactCorrection 52 (mA n) ≤ (9/2)/8000 := by
    apply (correction52_band hn).trans
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    linarith
  have h := location_row_price_cap (mul_nonneg hs ha0) (mul_nonneg hs hb0)
    (mul_nonneg hs hc0) (exactCorrection_nonneg _ _) ha hb hc hr
  rw [collectedSecond_scale, radiusPolynomialRoot104_scale hs] at h
  have h0 : 0 ≤ collectedSecond a b c+
      exactCorrection 52 (mA n)*radiusPolynomialRoot104 a b c^2 := by
    have hcol : 0 ≤ collectedSecond a b c := by unfold collectedSecond; positivity
    exact add_nonneg hcol (mul_nonneg (exactCorrection_nonneg _ _) (sq_nonneg _))
  have h' : (n : ℝ)^3*(collectedSecond a b c+
      exactCorrection 52 (mA n)*radiusPolynomialRoot104 a b c^2) ≤ (635/100000 : ℝ)^2 := by
    calc
      _ = ((n : ℝ)*sqrt n)^2*collectedSecond a b c+
          exactCorrection 52 (mA n)*((n : ℝ)*sqrt n*radiusPolynomialRoot104 a b c)^2 := by
        simp only [mul_pow, sq_sqrt (Nat.cast_nonneg n)]
        ring
      _ ≤ _ := h
  have hp := pow_le_pow_left₀ (mul_nonneg (by positivity) h0) h' 52
  convert hp using 1 <;> simp only [mA, Nat.cast_pow, mul_pow, ← pow_mul] <;> ring

theorem energy_price_normalized {n : ℕ} (hn : 8000 ≤ n) {a b c : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (ha : (n : ℝ)^2*a ≤ 205/100000)
    (hb : (n : ℝ)^2*b ≤ 161/100000)
    (hc : (n : ℝ)^2*c ≤ 79/100000) :
    (mA n : ℝ)^104*(a+b*sqrt (π/2)+2*c+
      exactCorrection 104 (mA n)*radiusPolynomialRoot104 a b c)^104 ≤ (575/100000 : ℝ)^104 := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : exactCorrection 104 (mA n) ≤ (63/10)/8000 := by
    apply (correction104_band hn).trans
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
    linarith
  have h := energy_row_price_cap (mul_nonneg (sq_nonneg _) ha0)
    (mul_nonneg (sq_nonneg _) hb0) (mul_nonneg (sq_nonneg _) hc0)
    (exactCorrection_nonneg _ _) ha hb hc hr
  rw [radiusPolynomialRoot104_scale (sq_nonneg (n : ℝ))] at h
  have h' : (n : ℝ)^2*(a+b*sqrt (π/2)+2*c+
      exactCorrection 104 (mA n)*radiusPolynomialRoot104 a b c) ≤ 575/100000 := by
    nlinarith only [h]
  have hz : 0 ≤ a+b*sqrt (π/2)+2*c+
      exactCorrection 104 (mA n)*radiusPolynomialRoot104 a b c := by
    have h1 := exactCorrection_nonneg 104 (mA n)
    have h2 := radiusPolynomialRoot104_nonneg a b c
    positivity
  have hp := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hz) h' 104
  simpa only [mul_pow, mA, Nat.cast_pow] using hp

end BstLean.Part292
