import BstLean.Part188Network

/-! Transfer unit-vector WF tests to the classifier's existing frame interface. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157
open BstLean.Part153 (nrm nrm_sq)

theorem frame_of_unit_tests {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Measure X) (e : X → Fin m → ℝ) {L : ℝ}
    (hunit : ∀ v : Fin m → ℝ, normSq v = 1 →
      ∫ x, (∑ j, e x j * v j) ^ 2 ∂μ ≤ L) (w : Fin m → ℝ) :
    ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ ≤ L * normSq w := by
  by_cases hw : normSq w = 0
  · have hz := eq_zero_of_normSq hw
    rw [hz]
    simp [normSq]
  · have hw0 : 0 < normSq w := lt_of_le_of_ne (normSq_nonneg w) (Ne.symm hw)
    set r := nrm w
    have hr : 0 < r := Real.sqrt_pos.mpr hw0
    have hr2 : r ^ 2 = normSq w := nrm_sq w
    set v : Fin m → ℝ := r⁻¹ • w
    have hv : normSq v = 1 := by
      have he : normSq v = (r⁻¹) ^ 2 * normSq w := by
        simp only [v, normSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      rw [he, inv_pow, ← hr2, inv_mul_cancel₀ (by positivity)]
    have he : ∀ x, (∑ j, e x j * w j) ^ 2 = r ^ 2 * (∑ j, e x j * v j) ^ 2 := by
      intro x
      have hdot : ∑ j, e x j * w j = r * ∑ j, e x j * v j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [v, Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [hdot, mul_pow]
    simp_rw [he]
    rw [integral_const_mul]
    have ht := mul_le_mul_of_nonneg_left (hunit v hv) (sq_nonneg r)
    rw [hr2] at ht
    rw [hr2]
    simpa only [mul_comm] using ht

theorem frameA_of_WF_tests {n : ℕ} (hn : 1 ≤ n) (D : Design n) {E : Set (Ret n)} {cf : ℝ}
    (hWF : ∀ c ∈ E, ∀ v : Fin (mA n) → ℝ, normSq v = 1 →
      (n : ℝ) * ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * v j) ^ 2
        ∂stdGauss (Fin n) ≤ cf) : FRAME_A_hyp D (cf / n) E := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  intro c hc w
  apply frame_of_unit_tests (stdGauss (Fin n))
    (fun ξ => eDir (D.bA c.1 c.2.1.1) (hStand D c ξ)) (L := cf / n) ?_ w
  intro v hv
  rw [le_div_iff₀ hnR]
  simpa only [mul_comm] using hWF c hc v hv

end BstLean.Part188
