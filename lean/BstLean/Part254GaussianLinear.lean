import BstLean.Part254Gaussian

namespace BstLean.Part254
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part182
open BstLean.Part153 (nrm nrm_nonneg)

theorem gaussianTail_nonneg (t : ℝ) : 0 ≤ gaussianTail t := by
  unfold gaussianTail
  positivity

theorem linear_gaussian_tail {n : ℕ} (v : Fin n → ℝ) {L t : ℝ}
    (hL : 0 < L) (hv : nrm v ≤ L) (ht : 0 ≤ t) :
    (stdGauss (Fin n)).real {ξ | t * L < |v ⬝ᵥ ξ|} ≤ gaussianTail t := by
  by_cases hv0 : v = 0
  · subst v
    have he : {ξ : Fin n → ℝ | t * L < |(0 : Fin n → ℝ) ⬝ᵥ ξ|} = ∅ := by
      ext ξ
      simp only [zero_dotProduct, abs_zero, mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact not_lt.mpr (mul_nonneg ht hL.le)
    rw [he, measureReal_empty]
    exact gaussianTail_nonneg t
  have hm : Measurable (fun ξ : Fin n → ℝ => ξ ⬝ᵥ uC v) := by
    unfold dotProduct
    fun_prop
  have hmap : (stdGauss (Fin n)).map (fun ξ => ξ ⬝ᵥ uC v) = gaussianReal 0 1 := by
    simpa only [uC_dot_self hv0, Real.toNNReal_one] using BstLean.Part131.stdGauss_dot (uC v)
  have hsub : {ξ : Fin n → ℝ | t * L < |v ⬝ᵥ ξ|} ⊆
      {ξ | t ≤ |ξ ⬝ᵥ uC v|} := by
    intro ξ hξ
    by_contra h
    have h' : |uC v ⬝ᵥ ξ| ≤ t := by
      rw [dotProduct_comm]
      exact (lt_of_not_ge h).le
    have hp := mul_le_mul hv h' (abs_nonneg _) hL.le
    change t * L < |v ⬝ᵥ ξ| at hξ
    rw [c_dot_uC hv0, abs_mul, abs_of_nonneg (nrm_nonneg v)] at hξ
    linarith
  have he : (stdGauss (Fin n)).real {ξ | t ≤ |ξ ⬝ᵥ uC v|} =
      (gaussianReal 0 1).real {x | t ≤ |x|} := by
    have hset : MeasurableSet {x : ℝ | t ≤ |x|} :=
      measurableSet_le measurable_const measurable_id.abs
    rw [← hmap, map_measureReal_apply hm hset]
    rfl
  exact (measureReal_mono hsub).trans (he.le.trans (gaussian_abs_tail_le t))

end BstLean.Part254
