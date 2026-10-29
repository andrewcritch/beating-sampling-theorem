import BstLean.Part207Quadratic
import BstLean.Part180HQ

/-! The HQ density bound with a cubic price and no split parameter. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)

/-- A density with a Jensen lower bound has a cubic Hellinger price. -/
theorem hell_of_cubic {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {R L : α → ℝ} (mR : Measurable R) (R0 : ∀ z, 0 ≤ R z)
    (iR : Integrable R μ) (i2 : Integrable (fun z => (R z - 1) ^ 2) μ)
    (iL : Integrable (fun z => |L z| ^ 3) μ) (hJ : ∀ z, exp (L z) ≤ R z) :
    BstLean.Part138.hellSq μ R (fun _ => 1) ≤
      (∫ z, (R z - 1) ^ 2 ∂μ) / 4 + 3 / 4 * ∫ z, |L z| ^ 3 ∂μ := by
  have mM : Measurable (fun z => max 0 (1 - R z) ^ 3) :=
    (measurable_const.max (measurable_const.sub mR)).pow_const 3
  have iM : Integrable (fun z => max 0 (1 - R z) ^ 3) μ := by
    refine Integrable.of_bound mM.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 : 0 ≤ max 0 (1 - R z) := le_max_left _ _
    have h1 : max 0 (1 - R z) ≤ 1 := max_le (by norm_num) (by linarith [R0 z])
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 3)]
    exact pow_le_one₀ h0 h1
  have isq : Integrable (fun z => √(R z * 1)) μ := by
    refine (iR.add (integrable_const (1 : ℝ))).mono'
      (mR.mul measurable_const).sqrt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_one]
    change √(R z) ≤ R z + 1
    nlinarith [Real.sq_sqrt (R0 z), Real.sqrt_nonneg (R z), sq_nonneg (√(R z) - 1)]
  have hH : BstLean.Part138.hellSq μ R (fun _ => 1) ≤
      (∫ z, (R z - 1) ^ 2 ∂μ) / 4 + 3 / 4 * ∫ z, max 0 (1 - R z) ^ 3 ∂μ := by
    have e : BstLean.Part138.hellSq μ R (fun _ => 1) =
        ∫ z, R z + 1 - 2 * √(R z * 1) ∂μ := by
      unfold BstLean.Part138.hellSq
      rw [integral_sub (f := fun z => R z + 1) (g := fun z => 2 * √(R z * 1))
          (iR.add (integrable_const 1)) (isq.const_mul 2),
        integral_add (f := R) (g := fun _ => (1 : ℝ)) iR (integrable_const 1),
        integral_const_mul]
    rw [e, ← integral_div, ← integral_const_mul,
      ← integral_add (i2.div_const _) (iM.const_mul _)]
    refine integral_mono ((iR.add (integrable_const 1)).sub (isq.const_mul 2))
      ((i2.div_const _).add (iM.const_mul _)) (fun z => ?_)
    rw [mul_one]
    have he : R z + 1 - 2 * √(R z) = (√(R z) - 1) ^ 2 := by
      nlinarith [Real.sq_sqrt (R0 z)]
    rw [he]
    exact BstLean.Part180.hq_point (R0 z)
  have hpt : ∀ z, max 0 (1 - R z) ^ 3 ≤ |L z| ^ 3 := by
    intro z
    apply pow_le_pow_left₀ (le_max_left _ _) _ 3
    apply max_le (abs_nonneg _)
    have h := add_one_le_exp (L z)
    have hl := neg_le_abs (L z)
    linarith [hJ z]
  have h := integral_mono iM iL hpt
  linarith

/-- The elementary cubic bound gives coefficient three for the triangle norm. -/
theorem hell_quadratic {n : ℕ} {R : (Fin n → ℝ) → ℝ} (mR : Measurable R)
    (R0 : ∀ z, 0 ≤ R z) (iR : Integrable R (stdGauss (Fin n)))
    (i2 : Integrable (fun z => (R z - 1) ^ 2) (stdGauss (Fin n)))
    (K b : ℝ) (u : Fin n → ℝ)
    (hJ : ∀ z, exp (K + b * (normSq z - n) + ∑ i, u i * z i) ≤ R z) :
    BstLean.Part138.hellSq (stdGauss (Fin n)) R (fun _ => 1) ≤
      (∫ z, (R z - 1) ^ 2 ∂stdGauss (Fin n)) / 4 +
        3 * (|K| + |b| * √(2 * (n : ℝ)) + √(∑ i, u i ^ 2)) ^ 3 := by
  obtain ⟨iL, hL⟩ := quadratic_cube K b u
  have h := hell_of_cubic mR R0 iR i2 iL hJ
  linarith

end BstLean.Part207
