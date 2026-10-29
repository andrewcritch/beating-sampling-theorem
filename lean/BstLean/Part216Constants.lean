import BstLean.Part216Clock

/-! Exact identification of the order18 and order24 paper constants. -/
namespace BstLean.Part216
open Real

noncomputable def k18 : ℝ := (2 * (2 ^ 9 * ((9 : ℕ).factorial : ℝ))) ^ ((18 : ℝ)⁻¹)
noncomputable def k24 : ℝ := (2 * (2 ^ 12 * ((12 : ℕ).factorial : ℝ))) ^ ((24 : ℝ)⁻¹)
noncomputable def Q18 (H Q : ℝ) : ℝ := H ^ (2 / 3 : ℝ) * Q ^ (1 / 3 : ℝ)

lemma k18_nonneg : 0 ≤ k18 := by unfold k18; positivity
lemma k24_nonneg : 0 ≤ k24 := by unfold k24; positivity
lemma k18_pow : k18 ^ 18 = 2 * (2 ^ 9 * ((9 : ℕ).factorial : ℝ)) :=
  rpow_inv_natCast_pow (by positivity) (by norm_num)
lemma k24_pow : k24 ^ 24 = 2 * (2 ^ 12 * ((12 : ℕ).factorial : ℝ)) :=
  rpow_inv_natCast_pow (by positivity) (by norm_num)

/-- The Gaussian term of BE18 has exactly the paper coefficient. -/
theorem energy18_gaussian_constant :
    sqrt 2 * k18 = 2 * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) := by
  apply (pow_left_inj₀ (mul_nonneg (sqrt_nonneg _) k18_nonneg)
    (by positivity : 0 ≤ 2 * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))
      (by norm_num : (18 : ℕ) ≠ 0)).mp
  have hr : ((2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)) ^ (18 : ℕ) =
      2 * ((9 : ℕ).factorial : ℝ) := by
    simpa only [Nat.cast_ofNat] using
      (rpow_inv_natCast_pow (x := 2 * ((9 : ℕ).factorial : ℝ)) (n := 18)
        (by positivity) (by norm_num))
  rw [mul_pow, mul_pow, k18_pow, hr]
  rw [show (18 : ℕ) = 2 * 9 by rfl, pow_mul, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The exponential term of BE18 has exactly the paper coefficient. -/
theorem energy18_exponential_constant :
    (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) =
      (2 : ℝ) ^ ((18 : ℝ)⁻¹) * ((18 : ℕ).factorial : ℝ) ^ ((18 : ℝ)⁻¹) :=
  mul_rpow (by norm_num) (by positivity)

/-- The order12 interpolation gives the exact paper weighted order18 factor. -/
theorem Q18_pow {H Q : ℝ} (hH : 0 ≤ H) (hQ : 0 ≤ Q) :
    Q18 H Q ^ 18 = H ^ 12 * Q ^ 6 := by
  unfold Q18
  rw [mul_pow, ← rpow_mul_natCast hH, ← rpow_mul_natCast hQ]
  norm_num

#print axioms energy18_gaussian_constant
#print axioms energy18_exponential_constant
#print axioms k24_pow
#print axioms Q18_pow
end BstLean.Part216
