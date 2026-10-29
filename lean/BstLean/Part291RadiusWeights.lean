import BstLean.Part291RWGeometry
import BstLean.Part215SharpRadius

/-! The radius moments are on the original Gaussian measure. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part182 BstLean.Part215
open BstLean.Part150 (thetaC)

theorem radius_weight_first {n : ℕ} (hn : 7 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    (∫ ξ, wN c τ ξ ∂stdGauss (Fin n)) ≤ radiusCoefficient n 1 (thetaC c τ) / n := by
  have h := BstLean.Part212.noncentral_inverse_radius (j := 1) (by norm_num) (by omega) c hτ
  rw [← radiusCoefficient_identity (by omega) c hτ] at h
  simp only [pow_one, div_eq_mul_inv] at h
  change (∫⁻ ξ, ENNReal.ofReal (wN c τ ξ) ∂stdGauss (Fin n)) ≤ _ at h
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_wN (by omega) c hτ)
    (ae_of_all _ (wN_nonneg c τ))] at h
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp h
  rw [← div_eq_mul_inv, radiusCoefficient_identity (by omega) c hτ]
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_nonneg (sq_nonneg τ)
    (add_nonneg (normSq_nonneg c) (mul_nonneg (by norm_num; linarith) (sq_nonneg τ)))

theorem radius_weight_second {n : ℕ} (hn : 7 ≤ n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) :
    (∫ ξ, wN c τ ξ ^ 2 ∂stdGauss (Fin n)) ≤
      (radiusCoefficient n 2 (thetaC c τ) / n) ^ 2 := by
  have h := BstLean.Part212.noncentral_inverse_radius (j := 2) (by norm_num) (by omega) c hτ
  rw [← radiusCoefficient_identity (by omega) c hτ] at h
  simp only [div_eq_mul_inv] at h
  change (∫⁻ ξ, ENNReal.ofReal (wN c τ ξ ^ 2) ∂stdGauss (Fin n)) ≤ _ at h
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_wN2 (by omega) c hτ)
    (ae_of_all _ fun _ => sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h

end BstLean.BlueprintLow
