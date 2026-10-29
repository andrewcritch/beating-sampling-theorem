import BstLean.Part219Axial
import BstLean.Part195Singular
import BstLean.Part208Radius
import BstLean.Part215SharpRadius

/-! The fixed-input overlap has the sharp inverse-radius variance allowance. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)
open BstLean.Part150 (thetaC)

lemma dot_euLip {n : ℕ} (u : Fin n → ℝ) :
    BstLean.Part148.EuLip (fun z => u ⬝ᵥ z) (nrm u) := by
  intro x y
  rw [← dotProduct_sub]
  exact abs_dot_le_nrm u (x - y)

lemma projection_abs_le_one {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (c : Fin n → ℝ) (τ : ℝ) (x) :
    |u ⬝ᵥ standPoint c τ x| ≤ 1 := by
  have h := abs_dot_le_nrm u (standPoint c τ x)
  simpa only [nrm, hu, standPoint, normSq_sphPt hn, sqrt_one, mul_one] using h

lemma projection_centered_integrable_sq {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (c : Fin n → ℝ) (τ : ℝ) (b : ℝ) :
    Integrable (fun x => (u ⬝ᵥ standPoint c τ x - b) ^ 2) (stdGauss (Fin n)) := by
  have hm : Measurable (fun x => (u ⬝ᵥ standPoint c τ x - b) ^ 2) := by
    have hdot : Continuous (fun z : Fin n → ℝ => u ⬝ᵥ z) := by
      unfold dotProduct
      fun_prop
    exact ((hdot.measurable.comp (measurable_standPoint c τ)).sub_const b).pow_const 2
  apply Integrable.of_bound hm.aestronglyMeasurable ((1 + |b|) ^ 2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((abs_sub _ _).trans (add_le_add (projection_abs_le_one hn hu c τ x) le_rfl)) 2

/-- Poincare at order two and the noncentral radius moment give the paper R_1/n. -/
theorem overlap_variance {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ x, (u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ) ^ 2 ∂stdGauss (Fin n)) ≤
      radiusCoefficient n 1 (thetaC c τ) / n := by
  have huN : nrm u = 1 := by simp only [nrm, hu, sqrt_one]
  have hPhi : BstLean.Part148.EuLip (fun z => u ⬝ᵥ z) 1 := by
    simpa only [huN] using dot_euLip u
  have hi := (invMoment_le (p := 1) (by omega) c hτ).1
  simp only [pow_one] at hi
  have hΓ : Integrable (fun x => (τ ^ 2 * (normSq (c + τ • x))⁻¹) ^ 1)
      (stdGauss (Fin n)) := by simpa only [pow_one] using hi.const_mul (τ ^ 2)
  have hgrad : ∀ᵐ x ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun x => u ⬝ᵥ sphPt (c + τ • x)) x (Pi.single i 1)) ^ 2 ≤
        τ ^ 2 * (normSq (c + τ • x))⁻¹ := by
    filter_upwards [ae_normSq_ne (by omega) c hτ.ne'] with x hx
    simpa only [one_pow, mul_one] using gradSq_sph_le c τ zero_le_one hPhi x hx
  have hr := BstLean.Part195.rotation_singular_dimension (q := 1) (by norm_num)
    (by omega) c hτ zero_le_one hPhi
    (fun x => mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))) hΓ hgrad
  have hm := dot_integral u (integrable_standPoint (by omega) c τ)
  change (∫ x, u ⬝ᵥ sphPt (c + τ • x) ∂stdGauss (Fin n)) = u ⬝ᵥ inputMean c τ at hm
  rw [hm] at hr
  simp only [BstLean.Part195.rotationConstant_one, one_pow, one_mul,
    show 2 * 1 = 2 by norm_num, sq_abs, pow_one, integral_const_mul] at hr
  have hiB := mul_le_mul_of_nonneg_left (BstLean.Part208.inverse_radius_mean (by omega) c hτ)
    (sq_nonneg τ)
  refine hr.trans (hiB.trans_eq ?_)
  rw [radiusCoefficient_identity (by omega) c hτ]
  congr 1
  ring

/-- The first absolute overlap deviation follows from the same order-two moment. -/
theorem overlap_absolute_deviation {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫ x, |u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ| ∂stdGauss (Fin n)) ≤
      √(radiusCoefficient n 1 (thetaC c τ) / n) := by
  have hi := ((integrable_dot u (integrable_standPoint (by omega) c τ)).sub
    (integrable_const (u ⬝ᵥ inputMean c τ))).abs
  have hi2 : Integrable (fun x => |u ⬝ᵥ standPoint c τ x - u ⬝ᵥ inputMean c τ| ^ 2)
      (stdGauss (Fin n)) := by
    simpa only [sq_abs] using projection_centered_integrable_sq (by omega) hu c τ
      (u ⬝ᵥ inputMean c τ)
  have h := sq_integral_le hi hi2
  simp only [sq_abs] at h
  exact Real.le_sqrt_of_sq_le (h.trans (overlap_variance hn hu c hτ))

#print axioms overlap_variance
#print axioms overlap_absolute_deviation
end BstLean.Part219
