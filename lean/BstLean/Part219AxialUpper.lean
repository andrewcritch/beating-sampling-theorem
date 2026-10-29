import BstLean.Part219Axial
import BstLean.Part208Radius

/-! Pairing a Gaussian input with its axial reflection bounds the axial mean. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

lemma inverse_length_integrable {n : ℕ} (hn : 4 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x => (nrm (c + τ • x))⁻¹) (stdGauss (Fin n)) := by
  have hi := (invMoment_le (p := 1) (by omega) c hτ).1
  simp only [pow_one] at hi
  have hm : Measurable (fun x : Fin n → ℝ => (nrm (c + τ • x))⁻¹) := by
    exact ((BstLean.Part130.measurable_normSq.comp
      (measurable_const.add (measurable_id.const_smul τ))).sqrt).inv
  refine ((integrable_const (1 : ℝ)).add hi).mono' hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (nrm_nonneg _))]
    have he : (nrm (c + τ • x))⁻¹ ^ 2 = (normSq (c + τ • x))⁻¹ := by
      rw [inv_pow, nrm_sq]
    dsimp only [Pi.add_apply]
    nlinarith [sq_nonneg ((nrm (c + τ • x))⁻¹ - 1)]

lemma reflection_axis_dot {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1) (x) :
    u ⬝ᵥ (reflection u *ᵥ x) = -(u ⬝ᵥ x) := by
  have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
  rw [reflection_apply, dotProduct_sub, dotProduct_smul, huu, smul_eq_mul, hu]
  ring

lemma normSq_axis_shift {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    (a τ : ℝ) (x : Fin n → ℝ) :
    normSq (a • u + τ • x) = a ^ 2 + τ ^ 2 * normSq x + 2 * a * τ * (u ⬝ᵥ x) := by
  rw [BstLean.Part133.normSq_add_eq, normSq_smul, normSq_smul, hu]
  change a ^ 2 * 1 + τ ^ 2 * normSq x + 2 * ((a • u) ⬝ᵥ (τ • x)) = _
  rw [smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  ring

lemma paired_inverse_sign {s R S a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hR : 0 < R) (hS : 0 < S) (hd : R ^ 2 - S ^ 2 = 4 * a * τ * s) :
    s / R + (-s) / S ≤ 0 := by
  rw [neg_div, ← sub_eq_add_neg, sub_nonpos]
  apply (div_le_div_iff₀ hR hS).mpr
  rcases le_total 0 s with hs | hs
  · have hp : 0 ≤ 4 * a * τ * s := by positivity
    have hSR : S ≤ R := by nlinarith
    exact mul_le_mul_of_nonneg_left hSR hs
  · have hp : 4 * a * τ * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs
    have hRS : R ≤ S := by nlinarith
    exact mul_le_mul_of_nonpos_left hRS hs

/-- The scalar reflected term is integrable before its expectation is compared. -/
lemma axial_ratio_integrable {n : ℕ} (hn : 4 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) (a : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun x => (u ⬝ᵥ x) / nrm (a • u + τ • x)) (stdGauss (Fin n)) := by
  have hi := ((integrable_dot u (integrable_standPoint (by omega) (a • u) τ)).sub
    ((inverse_length_integrable hn (a • u) hτ).const_mul a)).div_const τ
  apply hi.congr
  filter_upwards [ae_normSq_ne (by omega) (a • u) hτ.ne'] with x hx
  have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
  simp only [Pi.sub_apply, standPoint, sphPt_eq' hx, dotProduct_smul, dotProduct_add, huu,
    smul_eq_mul, mul_one]
  change ((1 / nrm (a • u + τ • x) * (a + τ * (u ⬝ᵥ x))) -
    a * (nrm (a • u + τ • x))⁻¹) / τ = (u ⬝ᵥ x) / nrm (a • u + τ • x)
  field_simp
  <;> ring

/-- Reflection pairing proves the nonpositive Gaussian correction in the axial mean. -/
theorem axial_ratio_mean_nonpos {n : ℕ} (hn : 4 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    (∫ x, (u ⬝ᵥ x) / nrm (a • u + τ • x) ∂stdGauss (Fin n)) ≤ 0 := by
  let f := fun x => (u ⬝ᵥ x) / nrm (a • u + τ • x)
  let Q := fun x => reflection u *ᵥ x
  have hQ : Measurable Q := (continuous_const.matrix_mulVec continuous_id).measurable
  have hp : MeasurePreserving Q (stdGauss (Fin n)) (stdGauss (Fin n)) :=
    ⟨hQ, reflection_distribution u⟩
  have hi : Integrable f (stdGauss (Fin n)) := axial_ratio_integrable hn hu a hτ
  have hiQ : Integrable (f ∘ Q) (stdGauss (Fin n)) := hp.integrable_comp_of_integrable hi
  have he : (∫ x, f (Q x) ∂stdGauss (Fin n)) = ∫ x, f x ∂stdGauss (Fin n) := by
    have hm := hi.aestronglyMeasurable
    rw [← hp.map_eq] at hm
    have hh := integral_map hQ.aemeasurable hm
    rw [hp.map_eq] at hh
    exact hh.symm
  have hs : ∀ᵐ x ∂stdGauss (Fin n), f x + f (Q x) ≤ 0 := by
    filter_upwards [ae_normSq_ne (by omega) (a • u) hτ.ne',
      hp.quasiMeasurePreserving.ae (ae_normSq_ne (by omega) (a • u) hτ.ne')] with x hx hxQ
    have hR : 0 < nrm (a • u + τ • x) :=
      sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) hx.symm)
    have hS : 0 < nrm (a • u + τ • Q x) :=
      sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) hxQ.symm)
    have hd : nrm (a • u + τ • x) ^ 2 - nrm (a • u + τ • Q x) ^ 2 =
        4 * a * τ * (u ⬝ᵥ x) := by
      rw [nrm_sq, nrm_sq, normSq_axis_shift hu, normSq_axis_shift hu,
        reflection_normSq, reflection_axis_dot hu]
      ring
    change (u ⬝ᵥ x) / nrm (a • u + τ • x) +
      (u ⬝ᵥ (reflection u *ᵥ x)) / nrm (a • u + τ • Q x) ≤ 0
    rw [reflection_axis_dot hu]
    exact paired_inverse_sign ha hτ.le hR hS hd
  have hsum := integral_nonpos_of_ae hs
  change Integrable (fun x => f (Q x)) (stdGauss (Fin n)) at hiQ
  rw [integral_add hi hiQ, he] at hsum
  change (∫ x, f x ∂stdGauss (Fin n)) ≤ 0
  linarith

/-- The mean coefficient is at most the shift length times the inverse-radius mean. -/
theorem inputMean_axial_upper {n : ℕ} (hn : 4 ≤ n) {u : Fin n → ℝ}
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 ≤ a) (hτ : 0 < τ) :
    u ⬝ᵥ inputMean (a • u) τ ≤
      a * ∫ x, (nrm (a • u + τ • x))⁻¹ ∂stdGauss (Fin n) := by
  have hratio := axial_ratio_mean_nonpos hn hu ha hτ
  have hiR := inverse_length_integrable hn (a • u) hτ
  have hiS := axial_ratio_integrable hn hu a hτ
  have he : ∀ᵐ x ∂stdGauss (Fin n),
      u ⬝ᵥ standPoint (a • u) τ x =
        a * (nrm (a • u + τ • x))⁻¹ + τ * ((u ⬝ᵥ x) / nrm (a • u + τ • x)) := by
    filter_upwards [ae_normSq_ne (by omega) (a • u) hτ.ne'] with x hx
    have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
    simp only [standPoint, sphPt_eq' hx, dotProduct_smul, dotProduct_add, huu,
      smul_eq_mul, mul_one]
    change 1 / nrm (a • u + τ • x) * (a + τ * (u ⬝ᵥ x)) = _
    ring
  unfold inputMean
  rw [← dot_integral u (integrable_standPoint (by omega) (a • u) τ)]
  rw [integral_congr_ae he, integral_add (hiR.const_mul a) (hiS.const_mul τ),
    integral_const_mul, integral_const_mul]
  nlinarith

#print axioms axial_ratio_mean_nonpos
#print axioms inputMean_axial_upper
end BstLean.Part219
