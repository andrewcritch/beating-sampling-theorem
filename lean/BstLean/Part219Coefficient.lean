import BstLean.Part219AxialUpper
import BstLean.Part219Radius
import BstLean.Part219IdealPointwise

/-! Mean-coefficient bounds from the inverse radius and the radius covariance. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part29 (stdGauss)

theorem inputMean_axial_upper_sharp {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    u ⬝ᵥ inputMean (a • u) τ ≤
      a * √(1 / (a ^ 2 + ((n : ℝ) - 4) * τ ^ 2)) := by
  have hi := inverse_length_integrable (by omega) (a • u) hτ
  have hi2 : Integrable (fun x => (nrm (a • u + τ • x))⁻¹ ^ 2)
      (stdGauss (Fin n)) := by
    simp only [inv_pow, nrm_sq]
    simpa only [pow_one] using (invMoment_le (p := 1) (by omega) (a • u) hτ).1
  have h := sq_integral_le hi hi2
  simp only [inv_pow, nrm_sq] at h
  have hh := BstLean.Part208.inverse_radius_mean (by omega) (a • u) hτ
  simp only [normSq_smul, hu, mul_one] at hh
  have hbound : (∫ x, (nrm (a • u + τ • x))⁻¹ ∂stdGauss (Fin n)) ≤
      √(1 / (a ^ 2 + ((n : ℝ) - 4) * τ ^ 2)) :=
    Real.le_sqrt_of_sq_le (h.trans (by simpa only [add_comm] using hh))
  exact (inputMean_axial_upper (by omega) hu ha hτ).trans
    (mul_le_mul_of_nonneg_left hbound ha)

lemma radius_times_latitude_mean {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ x, nrm (a • u + τ • x) * (u ⬝ᵥ standPoint (a • u) τ x)
      ∂stdGauss (Fin n)) = a := by
  have he : ∀ᵐ x ∂stdGauss (Fin n),
      nrm (a • u + τ • x) * (u ⬝ᵥ standPoint (a • u) τ x) =
        a + τ * (u ⬝ᵥ x) := by
    filter_upwards [ae_normSq_ne hn (a • u) hτ.ne'] with x hx
    have hR : nrm (a • u + τ • x) ≠ 0 := (sqrt_pos.mpr
      (lt_of_le_of_ne (normSq_nonneg _) hx.symm)).ne'
    have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
    rw [standPoint, sphPt_eq' hx, dotProduct_smul, dotProduct_add,
      dotProduct_smul, dotProduct_smul, huu, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one]
    change nrm (a • u + τ • x) * (1 / nrm (a • u + τ • x) * _) = _
    field_simp
  rw [integral_congr_ae he]
  have hi : Integrable (fun x : Fin n → ℝ => u ⬝ᵥ x) (stdGauss (Fin n)) :=
    BstLean.Part112.int_dw u
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
  have hz : (∫ x : Fin n → ℝ, u ⬝ᵥ x ∂stdGauss (Fin n)) = 0 :=
    BstLean.Part112.integral_dw u
  simp only [hz, mul_zero, add_zero, integral_const, probReal_univ, one_smul]

/-- The covariance step exposes only the latitude variance that it consumes. -/
theorem inputMean_bias_of_variance {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ V : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) (hV : 0 ≤ V)
    (hv : (∫ x, (u ⬝ᵥ standPoint (a • u) τ x - u ⬝ᵥ inputMean (a • u) τ) ^ 2
      ∂stdGauss (Fin n)) ≤ V ^ 2) :
    |u ⬝ᵥ inputMean (a • u) τ - a / rhoC (a • u) τ| ≤
      τ ^ 2 / rhoC (a • u) τ ^ 2 + τ / rhoC (a • u) τ * V := by
  let c := a • u
  let ρ := rhoC c τ
  let M := ∫ x, nrm (c + τ • x) ∂stdGauss (Fin n)
  let α := u ⬝ᵥ inputMean c τ
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hρ : 0 < ρ := sqrt_pos.mpr (add_pos_of_nonneg_of_pos
    (normSq_nonneg c) (mul_pos hnR (sq_pos_of_pos hτ)))
  obtain ⟨hi, hvi, hvR, hlo, hhi⟩ := radius_stats hn c hτ
  have hmeas : Measurable (fun x => u ⬝ᵥ standPoint c τ x) := by
    have hd : Continuous (fun z : Fin n → ℝ => u ⬝ᵥ z) := by unfold dotProduct; fun_prop
    exact hd.measurable.comp (measurable_standPoint c τ)
  have hc := radius_covariance hi hvi hmeas (projection_abs_le_one hn hu c τ)
  rw [radius_times_latitude_mean hn hu a hτ,
    dot_integral u (integrable_standPoint hn c τ)] at hc
  change |a - M * α| ≤ _ at hc
  have hsR : √(∫ x, (nrm (c + τ • x) - M) ^ 2 ∂stdGauss (Fin n)) ≤ τ := by
    exact (sqrt_le_iff).mpr ⟨hτ.le, hvR⟩
  have hsz : √(∫ x, (u ⬝ᵥ standPoint c τ x - α) ^ 2 ∂stdGauss (Fin n)) ≤ V :=
    (sqrt_le_iff).mpr ⟨hV, hv⟩
  have hcov : |a - M * α| ≤ τ * V := hc.trans
    (mul_le_mul hsR hsz (sqrt_nonneg _) hτ.le)
  have hα := inputMean_axial_nonneg hn u ha hτ
  have hα1 := (abs_le.mp (inputMean_coefficient_abs hn hu c τ)).2
  have hM : 0 ≤ ρ - M := sub_nonneg.mpr hhi
  have hM' : ρ - M ≤ τ ^ 2 / ρ := by linarith
  have he : ρ * α - a = (ρ - M) * α + (M * α - a) := by ring
  have hB : |ρ * α - a| ≤ τ ^ 2 / ρ + τ * V := by
    rw [he]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hM, abs_of_nonneg hα, abs_sub_comm]
    exact add_le_add ((mul_le_mul_of_nonneg_left hα1 hM).trans
      (by simpa only [mul_one] using hM')) hcov
  have he' : |α - a / ρ| = |ρ * α - a| / ρ := by
    have hfrac : α - a / ρ = (ρ * α - a) / ρ := by field_simp
    rw [hfrac, abs_div, abs_of_pos hρ]
  change |α - a / ρ| ≤ _
  rw [he']
  refine (div_le_div_of_nonneg_right hB hρ.le).trans_eq ?_
  change (τ ^ 2 / ρ + τ * V) / ρ = τ ^ 2 / ρ ^ 2 + τ / ρ * V
  ring

#print axioms inputMean_axial_upper_sharp
#print axioms inputMean_bias_of_variance
end BstLean.Part219
