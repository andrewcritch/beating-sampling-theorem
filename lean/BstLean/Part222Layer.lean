import BstLean.Part195Rotation
import BstLean.Part153Bin

/-! The normalized ReLU radius has the paper mean deficit and order-32 allowance. -/
namespace BstLean.Part222
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153

noncomputable def layerRoot (m : ℕ) (x : Fin m → ℝ) : ℝ :=
  √(2 / (m : ℝ)) * nrm (reluV x)

noncomputable def layerAllowance (m : ℕ) : ℝ :=
  BstLean.Part195.rotationConstant 16 * √(2 / (m : ℝ)) + 5 / (2 * m)

lemma layerRoot_nonneg (m : ℕ) (x : Fin m → ℝ) : 0 ≤ layerRoot m x := by
  unfold layerRoot
  exact mul_nonneg (sqrt_nonneg _) (nrm_nonneg _)

lemma layerRoot_lip (m : ℕ) :
    BstLean.Part148.EuLip (layerRoot m) (√(2 / (m : ℝ))) := by
  intro x y
  unfold layerRoot
  rw [← mul_sub, abs_mul, abs_of_nonneg (sqrt_nonneg _)]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_left (euLip_nrm_reluV x y) (sqrt_nonneg (2 / (m : ℝ)))

lemma layerRoot_memLp (m : ℕ) {q : ℕ} (hq : 1 ≤ q) :
    MemLp (layerRoot m) (2*q : ℕ) (stdGauss (Fin m)) := by
  have hc : Continuous (layerRoot m) :=
    (layerRoot_lip m).continuous (sqrt_nonneg _)
  apply (integrable_norm_rpow_iff hc.aestronglyMeasurable
    (by exact_mod_cast (show 2*q ≠ 0 by omega)) (ENNReal.natCast_ne_top _)).1
  have hi := (nrm_reluV_moment m hq).1.const_mul (√(2 / (m : ℝ)) ^ (2*q))
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
    layerRoot, abs_mul, abs_of_nonneg (sqrt_nonneg _),
    abs_of_nonneg (nrm_nonneg _), mul_pow] using hi

lemma layerRoot_second {m : ℕ} (hm : 1 ≤ m) :
    ∫ x, layerRoot m x ^ 2 ∂stdGauss (Fin m) = 1 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [layerRoot, mul_pow, sq_sqrt (by positivity : 0 ≤ 2 / (m : ℝ))]
  rw [integral_const_mul, (int_normSq_reluV_std m).2]
  field_simp

lemma layerRoot_fourth {m : ℕ} (hm : 1 ≤ m) :
    ∫ x, layerRoot m x ^ 4 ∂stdGauss (Fin m) = 1 + 5 / m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : ∀ x : Fin m → ℝ, layerRoot m x ^ 4 =
      (2 / (m : ℝ)) ^ 2 * (∑ j, relu (x j)^2)^2 := by
    intro x
    rw [show (4 : ℕ) = 2*2 from rfl, pow_mul]
    simp only [layerRoot, mul_pow, nrm_sq, normSq, reluV,
      sq_sqrt (by positivity : 0 ≤ 2 / (m : ℝ))]
  simp_rw [he]
  rw [integral_const_mul]
  have h4 : Integrable (fun x : ℝ => (relu x ^ 2)^2) (gaussianReal 0 1) := by
    simpa only [← pow_mul] using integrable_relu_pow 4
  unfold stdGauss
  rw [pi_sum_sq (integrable_relu_pow 2) h4, int_relu_sq, Fintype.card_fin]
  simp_rw [sq_sq]
  rw [int_relu_four]
  field_simp
  <;> ring

/-- The mean deficit uses the exact energy variance, with coefficient five. -/
theorem layerRoot_mean_deficit {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ 1 - ∫ x, layerRoot m x ∂stdGauss (Fin m) ∧
    1 - ∫ x, layerRoot m x ∂stdGauss (Fin m) ≤ 5 / (2*m) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  have hf := layerRoot_memLp m (q := 1) (by norm_num)
  have hi := hf.integrable (by norm_num)
  have h2 := hf.integrable_sq
  have h4 := (layerRoot_memLp m (q := 2) (by norm_num)).integrable_norm_pow (by norm_num)
  simp only [Real.norm_eq_abs, abs_of_nonneg (layerRoot_nonneg _ _)] at h4
  have hD : Integrable (fun x => (layerRoot m x-1)^2) (stdGauss (Fin m)) :=
    (hf.sub (memLp_const (1 : ℝ))).integrable_sq
  have hV : Integrable (fun x => (layerRoot m x^2-1)^2) (stdGauss (Fin m)) := by
    have he : (fun x => (layerRoot m x^2-1)^2) =
        (fun x => layerRoot m x^4 - 2*layerRoot m x^2 + 1) := by funext x; ring
    rw [he]
    exact (h4.sub (h2.const_mul 2)).add (integrable_const 1)
  have eD : (∫ x, (layerRoot m x-1)^2 ∂stdGauss (Fin m)) =
      2*(1-∫ x, layerRoot m x ∂stdGauss (Fin m)) := by
    have he : (fun x => (layerRoot m x-1)^2) =
        (fun x => layerRoot m x^2 - 2*layerRoot m x + 1) := by funext x; ring
    rw [he, integral_add (f := fun x => layerRoot m x^2 - 2*layerRoot m x)
      (g := fun _ => (1 : ℝ)) (h2.sub (hi.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun x => layerRoot m x^2) (g := fun x => 2*layerRoot m x)
        h2 (hi.const_mul 2), integral_const_mul, layerRoot_second hm]
    simp
    <;> ring
  have eV : (∫ x, (layerRoot m x^2-1)^2 ∂stdGauss (Fin m)) = 5/(m : ℝ) := by
    have he : (fun x => (layerRoot m x^2-1)^2) =
        (fun x => layerRoot m x^4 - 2*layerRoot m x^2 + 1) := by funext x; ring
    rw [he, integral_add (f := fun x => layerRoot m x^4 - 2*layerRoot m x^2)
      (g := fun _ => (1 : ℝ)) (h4.sub (h2.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun x => layerRoot m x^4) (g := fun x => 2*layerRoot m x^2)
        h4 (h2.const_mul 2), integral_const_mul,
      layerRoot_fourth hm, layerRoot_second hm]
    simp
    <;> ring
  have hcomp : (∫ x, (layerRoot m x-1)^2 ∂stdGauss (Fin m)) ≤
      ∫ x, (layerRoot m x^2-1)^2 ∂stdGauss (Fin m) := by
    apply integral_mono hD hV
    intro x
    have h : 0 ≤ (layerRoot m x-1)^2 * layerRoot m x * (layerRoot m x+2) := by
      have := layerRoot_nonneg m x
      positivity
    nlinarith [h]
  have h0 : 0 ≤ ∫ x, (layerRoot m x-1)^2 ∂stdGauss (Fin m) :=
    integral_nonneg fun x => sq_nonneg _
  rw [eD] at h0 hcomp
  rw [eV] at hcomp
  constructor
  · linarith
  · have he : 5 / (2*(m : ℝ)) = (5/(m : ℝ))/2 := by ring
    rw [he]
    linarith

#print axioms layerRoot_mean_deficit
end BstLean.Part222
