import BstLean.Part212GammaTail
import BstLean.Part212Laplace

/-! Scalar Laplace majorants retain the noncentral radius parameter. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal

theorem inverse_gamma_identity (k : ℕ) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (k.factorial : ℝ) * ENNReal.ofReal (R⁻¹ ^ (k + 1)) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ k * exp (-(R * t))) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ k * exp (-(R * t))) (Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := R)
        (by have h := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num) hR)
  have hv := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((k + 1 : ℕ) : ℝ)) (r := R) (by positivity) hR
  have hj : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
  have hx (x : ℝ) : x ^ ((k : ℝ) + 1) = x ^ (k + 1) := by
    rw [← hj, Real.rpow_natCast]
  rw [hj, Real.Gamma_nat_eq_factorial] at hv
  simp only [add_sub_cancel_right, Real.rpow_natCast, hx, one_div] at hv
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [hv, ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hR.le) _)]
    exact mul_comm _ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (pow_nonneg ht.le _) (exp_pos _).le

/-- The radial substitution gives a pointwise majorant without discarding the noncentral factor. -/
theorem gaussian_gamma_pointwise (k n : ℕ) (hn : 2 * k + 5 ≤ n)
    {Λ t : ℝ} (hΛ : 0 ≤ Λ) (ht : 0 ≤ t) :
    t ^ k * exp (-(Λ * gammaMobius t)) * ((√(1 + 2 * t))⁻¹) ^ n ≤
      gammaMobius t ^ k * exp (-((n : ℝ) - 2 * k - 4 + Λ) * gammaMobius t) /
        (1 + 2 * t) ^ 2 := by
  let A : ℝ := 1 + 2 * t
  let a : ℝ := (n : ℝ) / 2 - k - 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hnR : (2 * (k : ℝ) + 5) ≤ n := by exact_mod_cast hn
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hv : 0 ≤ gammaMobius t := div_nonneg ht hA.le
  have htA : t = gammaMobius t * A := by unfold gammaMobius; dsimp [A]; field_simp
  have hsq : ((√A)⁻¹) ^ n = A ^ (-(n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hA.le, ← Real.rpow_natCast,
      ← Real.rpow_mul hA.le]
    congr 1
    ring
  have hpow : A ^ k * A ^ (-(n : ℝ) / 2) = A ^ (-a) / A ^ 2 := by
    rw [← Real.rpow_natCast A k, ← Real.rpow_add hA,
      ← Real.rpow_two, ← Real.rpow_sub hA]
    congr 1
    dsimp [a]
    ring
  have hlog : 2 * gammaMobius t ≤ log A := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hA)
    rw [Real.log_inv] at h
    have he : 1 - A⁻¹ = 2 * gammaMobius t := by
      unfold gammaMobius
      dsimp [A]
      field_simp
      ring
    linarith
  have hexp : A ^ (-a) ≤ exp (-(2 * a * gammaMobius t)) := by
    rw [Real.rpow_def_of_pos hA]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hlog ha]
  have hfactor : 0 ≤ gammaMobius t ^ k / A ^ 2 * exp (-(Λ * gammaMobius t)) :=
    mul_nonneg (div_nonneg (pow_nonneg hv _) (sq_nonneg A)) (exp_pos _).le
  have hpT : t ^ k = gammaMobius t ^ k * A ^ k := by
    calc t ^ k = (gammaMobius t * A) ^ k := congrArg (fun x : ℝ => x ^ k) htA
      _ = _ := mul_pow _ _ _
  calc t ^ k * exp (-(Λ * gammaMobius t)) * ((√A)⁻¹) ^ n
      = gammaMobius t ^ k * exp (-(Λ * gammaMobius t)) *
        (A ^ k * A ^ (-(n : ℝ) / 2)) := by rw [hpT, hsq]; ring
    _ = (gammaMobius t ^ k / A ^ 2 * exp (-(Λ * gammaMobius t))) * A ^ (-a) := by
      rw [hpow]; ring
    _ ≤ (gammaMobius t ^ k / A ^ 2 * exp (-(Λ * gammaMobius t))) *
        exp (-(2 * a * gammaMobius t)) := mul_le_mul_of_nonneg_left hexp hfactor
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      have he : -(Λ * gammaMobius t) + -(2 * a * gammaMobius t) =
          -((n : ℝ) - 2 * k - 4 + Λ) * gammaMobius t := by dsimp [a]; ring
      rw [he]
      dsimp [A]
      ring
end BstLean.Part212
