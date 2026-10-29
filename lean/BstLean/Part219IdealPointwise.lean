import BstLean.Part219Secant
import BstLean.Part219Overlap

/-! The deterministic ideal average splits into a latitude term and a sharp remainder. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC)
open BstLean.Part29 (stdGauss)

lemma inputMean_coefficient_abs {n : ℕ} (hn : 1 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (c : Fin n → ℝ) (τ : ℝ) :
    |u ⬝ᵥ inputMean c τ| ≤ 1 := by
  unfold inputMean
  rw [← dot_integral u (integrable_standPoint hn c τ)]
  refine (abs_integral_le_integral_abs).trans ?_
  have h := integral_mono_ae (integrable_dot u (integrable_standPoint hn c τ)).abs
    (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall
      (projection_abs_le_one hn hu c τ))
  simpa only [integral_const, probReal_univ, one_smul] using h

theorem overlap_deviation_axial {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (q : ℝ) {x : Fin n → ℝ} (hx : normSq x = 1) :
    (∫ z, |x ⬝ᵥ standPoint (a • u) τ z - q| ∂stdGauss (Fin n)) ≤
      √(radiusCoefficient n 1 (thetaC (a • u) τ) / n) +
        (u ⬝ᵥ inputMean (a • u) τ) *
          |x ⬝ᵥ u - u ⬝ᵥ inputMean (a • u) τ| +
        |(u ⬝ᵥ inputMean (a • u) τ) ^ 2 - q| := by
  let α := u ⬝ᵥ inputMean (a • u) τ
  have hα : 0 ≤ α := inputMean_axial_nonneg (by omega) u ha hτ
  have hm : x ⬝ᵥ inputMean (a • u) τ = α * (x ⬝ᵥ u) := by
    rw [inputMean_axial (by omega) hu a hτ, dotProduct_smul, smul_eq_mul]
  have hi := integrable_dot x (integrable_standPoint (by omega) (a • u) τ)
  have hp : ∀ z : Fin n → ℝ,
      |x ⬝ᵥ standPoint (a • u) τ z - q| ≤
        |x ⬝ᵥ standPoint (a • u) τ z - x ⬝ᵥ inputMean (a • u) τ| +
          (α * |x ⬝ᵥ u - α| + |α ^ 2 - q|) := by
    intro z
    have he : x ⬝ᵥ standPoint (a • u) τ z - q =
        (x ⬝ᵥ standPoint (a • u) τ z - x ⬝ᵥ inputMean (a • u) τ) +
          (α * (x ⬝ᵥ u - α) + (α ^ 2 - q)) := by rw [hm]; ring
    rw [he]
    refine (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _)) |>.trans_eq ?_
    rw [abs_mul, abs_of_nonneg hα]
  have h := integral_mono_ae (hi.sub (integrable_const q)).abs
    (((hi.sub (integrable_const _)).abs).add (integrable_const _))
    (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply, Pi.sub_apply] at h
  have hci : Integrable (fun z => |x ⬝ᵥ standPoint (a • u) τ z - x ⬝ᵥ inputMean (a • u) τ|)
      (stdGauss (Fin n)) := (hi.sub (integrable_const _)).abs
  rw [integral_add hci (integrable_const _),
    integral_const, probReal_univ, one_smul] at h
  exact h.trans (by
    have hh := overlap_absolute_deviation hn hx (a • u) hτ
    linarith)

/-- This is the paper remainder estimate for the actual projected kernel average. -/
theorem ideal_average_sharp_pointwise {n : ℕ} (hn : 5 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ q : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ)
    (hq : q ∈ Icc (0 : ℝ) (27 / 50)) {x : Fin n → ℝ} (hx : normSq x = 1) :
    nrm (∫ z, idealRemainder q x (standPoint (a • u) τ z) ∂stdGauss (Fin n)) ≤
      (77 / 100) * (√(radiusCoefficient n 1 (thetaC (a • u) τ) / n) +
        (u ⬝ᵥ inputMean (a • u) τ) *
          |x ⬝ᵥ u - u ⬝ᵥ inputMean (a • u) τ| +
        |(u ⬝ᵥ inputMean (a • u) τ) ^ 2 - q|) := by
  have hm := (continuous_idealRemainder q x).measurable.comp
    (measurable_standPoint (a • u) τ)
  have hN : Integrable (fun z => nrm (idealRemainder q x (standPoint (a • u) τ z)))
      (stdGauss (Fin n)) :=
    Integrable.of_bound (BstLean.Part130.measurable_normSq.comp hm).sqrt.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (nrm_nonneg _)]
        exact idealRemainder_le_one q hx (normSq_sphPt (by omega) _))
  have hi := BstLean.Part200.integrable_vector_of_nrm hm hN
  have hdot := (integrable_dot x (integrable_standPoint (by omega) (a • u) τ)).sub
    (integrable_const q)
  refine (nrm_integral_le hi hN).trans ?_
  have h := integral_mono_ae hN
    (hdot.abs.const_mul (77 / 100)) (Filter.Eventually.of_forall fun z =>
      idealRemainder_sharp hq hx (normSq_sphPt (by omega) _))
  rw [integral_const_mul] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (overlap_deviation_axial hn hu ha hτ q hx) (by norm_num))

#print axioms inputMean_coefficient_abs
#print axioms overlap_deviation_axial
#print axioms ideal_average_sharp_pointwise
end BstLean.Part219
