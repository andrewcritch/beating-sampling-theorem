import BstLean.Part228Normalized
import BstLean.Part228Log

/-! Cancellation identities for the numerical latitude certificates. -/
namespace BstLean.Part228
open Real
open BstLean.Part197 (logOneAddSum)

/-- This is the cancellation formula in the paper's block evaluator. -/
theorem normalizedExponent_cancellation {n : ℕ} (hn : 1 ≤ n) {θ b u : ℝ}
    (hθ : θ ≠ 0) (hu : 1 - u ≠ 0) :
    normalizedExponent n θ b u =
      (-log (1 - u) + log (1 + endpointRatio b * u)) / 2 +
      n / 2 * (- (endpointRatio b - (1 - θ) / θ) * u +
        ((1 - θ) / θ) * u ^ 2 / (1 - u) +
        (endpointRatio b * u - log (1 + endpointRatio b * u))) := by
  have hn' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  unfold normalizedExponent
  rw [hn']
  field_simp
  <;> ring

/-- The linear cancellation term has a small numerator at either endpoint. -/
theorem endpointRatio_sub {θ b : ℝ} (hθ : θ ≠ 0) (hb : 1 - b ^ 2 ≠ 0) :
    endpointRatio b - (1 - θ) / θ =
      (b ^ 2 - (1 - θ)) / (θ * (1 - b ^ 2)) := by
  unfold endpointRatio
  field_simp
  <;> ring

/-- An algebraic root coordinate removes the large dimension from the enclosure. -/
theorem normalizedExponent_scaled {n : ℕ} (hn : 1 ≤ n) {θ b x k d : ℝ}
    (hθ : θ ≠ 0) (hx : (n : ℝ) * x ^ 2 = 1)
    (hu : 1 - k * x ≠ 0)
    (hd : endpointRatio b - (1 - θ) / θ = x * d) :
    normalizedExponent n θ b (k * x) =
      (-log (1 - k * x) + log (1 + endpointRatio b * (k * x))) / 2 +
      (-d * k + ((1 - θ) / θ) * k ^ 2 / (1 - k * x) +
        n * (endpointRatio b * (k * x) -
          log (1 + endpointRatio b * (k * x)))) / 2 := by
  rw [normalizedExponent_cancellation hn hθ hu, hd]
  have h1 : (n : ℝ) * (x * d * (k * x)) = d * k := by
    calc _ = ((n : ℝ) * x ^ 2) * (d * k) := by ring
      _ = _ := by rw [hx]; ring
  have h2 : (n : ℝ) * (((1 - θ) / θ) * (k * x) ^ 2 / (1 - k * x)) =
      ((1 - θ) / θ) * k ^ 2 / (1 - k * x) := by
    calc _ = ((n : ℝ) * x ^ 2) * (((1 - θ) / θ) * k ^ 2 / (1 - k * x)) := by ring
      _ = _ := by rw [hx]; ring
  nlinarith only [h1, h2]

/-- The degree-six cancellation polynomial after multiplication by the dimension. -/
noncomputable def scaledCancellation6 (a k x : ℝ) : ℝ :=
  (a*k)^2/2 - (a*k)^3*x/3 + (a*k)^4*x^2/4 -
    (a*k)^5*x^3/5 + (a*k)^6*x^4/6

theorem scaledCancellation6_error {n : ℕ} {a k x : ℝ}
    (hx : 0 ≤ x) (hnx : (n : ℝ) * x ^ 2 = 1) (hv : |a * k * x| < 1) :
    (n : ℝ) * (a * k * x - log (1 + a * k * x)) ≤
      scaledCancellation6 a k x +
        |a * k| ^ 7 * x ^ 5 / (7 * (1 - |a * k * x|)) := by
  have he := (abs_le.mp (log_one_add_remainder_sharp hv 6)).1
  have hpoly : (n : ℝ) * (a*k*x - logOneAddSum 6 (a*k*x)) =
      scaledCancellation6 a k x := by
    norm_num [logOneAddSum, Finset.sum_range_succ, scaledCancellation6]
    linear_combination (a*k)^2/2 * hnx - (a*k)^3*x/3 * hnx +
      (a*k)^4*x^2/4 * hnx - (a*k)^5*x^3/5 * hnx + (a*k)^6*x^4/6 * hnx
  have herr : (n : ℝ) * (|a*k*x|^7 / (7 * (1 - |a*k*x|))) =
      |a*k|^7*x^5 / (7 * (1 - |a*k*x|)) := by
    rw [abs_mul, abs_of_nonneg hx, mul_pow]
    calc _ = ((n : ℝ) * x^2) * (|a*k|^7*x^5 / (7 * (1 - |a*k| * x))) := by ring
      _ = _ := by rw [hnx]; ring
  have h := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  norm_num only [Nat.cast_ofNat] at h
  linarith [hpoly, herr]

/-- A rational expression bounds the normalized exponent, for either tilt sign. -/
noncomputable def scaledExponentBound (θ a x k d : ℝ) : ℝ :=
  ((k*x)/(1-k*x) + a*k*x)/2 +
    (-d*k + ((1-θ)/θ)*k^2/(1-k*x) + scaledCancellation6 a k x +
      |a*k|^7*x^5/(7*(1-|a*k*x|)))/2

theorem normalizedExponent_le_scaled {n : ℕ} (hn : 1 ≤ n) {θ b x k d : ℝ}
    (hθ : θ ≠ 0) (hx : 0 ≤ x) (hnx : (n : ℝ) * x ^ 2 = 1)
    (hu : 0 < 1 - k * x) (hv : |endpointRatio b * k * x| < 1)
    (hd : endpointRatio b - (1 - θ) / θ = x * d) :
    normalizedExponent n θ b (k*x) ≤
      scaledExponentBound θ (endpointRatio b) x k d := by
  rw [normalizedExponent_scaled hn hθ hnx hu.ne' hd]
  have hlog1 := one_sub_inv_le_log_of_pos hu
  have hvpos : 0 < 1 + endpointRatio b * k * x := by
    have := (abs_lt.mp hv).1
    linarith
  have hlog2 := log_le_sub_one_of_pos hvpos
  have hrat : (1 - k*x)⁻¹ - 1 = (k*x)/(1-k*x) := by field_simp; ring
  have hrem := scaledCancellation6_error (a := endpointRatio b) (k := k) hx hnx hv
  unfold scaledExponentBound
  simp only [mul_assoc] at hlog2 hrem ⊢
  linarith

end BstLean.Part228
