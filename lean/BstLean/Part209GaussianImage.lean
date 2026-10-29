import BstLean.Part209Row
import BstLean.Part153Bin

/-! Gaussian image moments depend on the output dimension, not the input dimension. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)

variable {n m : ℕ}

lemma dot_square_integral (a : Fin m → ℝ) :
    Integrable (fun w => dotp w a ^ 2) (stdGauss (Fin m)) ∧
      (∫ w, dotp w a ^ 2 ∂stdGauss (Fin m)) = normSq a := by
  have hm := (measurable_dot_left a).pow_const 2
  have hl := BstLean.Part151.dot_mom 1 a
  have hg : BstLean.Part29.gaussMom 2 = 1 := BstLean.Part151.gaussMom_two
  simp only [Nat.mul_one, hg, pow_one, one_mul] at hl
  have hi : Integrable (fun w => dotp w a ^ 2) (stdGauss (Fin m)) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ fun w => sq_nonneg (dotp w a))).mp
        (by change (∫⁻ w, ENNReal.ofReal ((w ⬝ᵥ a) ^ 2) ∂stdGauss (Fin m)) ≠ ⊤
            rw [hl]; exact ENNReal.ofReal_ne_top)
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun w => sq_nonneg (dotp w a))
  change ENNReal.ofReal (∫ w, dotp w a ^ 2 ∂stdGauss (Fin m)) =
    ∫⁻ w, ENNReal.ofReal ((w ⬝ᵥ a) ^ 2) ∂stdGauss (Fin m) at he
  rw [hl] at he
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun w => sq_nonneg (dotp w a)),
    ENNReal.toReal_ofReal (normSq_nonneg a)] using hh

lemma image_second_moment (T : Matrix (Fin n) (Fin m) ℝ) :
    Integrable (fun w => nrm (T *ᵥ w) ^ 2) (stdGauss (Fin m)) ∧
      (∫ w, nrm (T *ᵥ w) ^ 2 ∂stdGauss (Fin m)) ≤ (n : ℝ) * opN T ^ 2 := by
  have he : ∀ w, nrm (T *ᵥ w) ^ 2 = ∑ i, dotp w (T i) ^ 2 := by
    intro w
    rw [nrm_sq]
    unfold normSq
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact dotProduct_comm _ _
  simp_rw [he]
  have hi := fun i (_ : i ∈ Finset.univ) => (dot_square_integral (T i)).1
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  simp_rw [(dot_square_integral _).2]
  have h := fro_le Tᵀ
  rw [opN_transpose] at h
  change (∑ i, ∑ j, T j i ^ 2) ≤ (n : ℝ) * opN T ^ 2 at h
  rw [Finset.sum_comm] at h
  exact h

/-- The output dimension controls the Gaussian image moment even when `m` is much larger. -/
theorem gaussian_image_moment (T : Matrix (Fin n) (Fin m) ℝ) {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun w => nrm (T *ᵥ w) ^ (2 * P)) (stdGauss (Fin m)) ∧
      (∫ w, nrm (T *ᵥ w) ^ (2 * P) ∂stdGauss (Fin m)) ≤
        (opN T * (sqrt (n : ℝ) + gaussMomConst P)) ^ (2 * P) := by
  have hL : EuLip (fun w => nrm (T *ᵥ w)) (opN T) := by
    intro w z
    calc |nrm (T *ᵥ w) - nrm (T *ᵥ z)| ≤ nrm (T *ᵥ w - T *ᵥ z) := abs_nrm_sub_le _ _
      _ = nrm (T *ᵥ (w - z)) := by rw [Matrix.mulVec_sub]
      _ ≤ opN T * nrm (w - z) := nrm_mulVec_le _ _
  have hm : Measurable (fun w => nrm (T *ᵥ w)) := (hL.continuous (opN_nonneg T)).measurable
  obtain ⟨hi, _, _⟩ := gaussConc_mgf_sharp (opN_nonneg T) hL 0
  obtain ⟨hi2, hb2⟩ := image_second_moment T
  have hmean : (∫ w, nrm (T *ᵥ w) ∂stdGauss (Fin m)) ≤ opN T * sqrt (n : ℝ) := by
    have hs := (sq_integral_le hi hi2).trans hb2
    have he : (opN T * sqrt (n : ℝ)) ^ 2 = (n : ℝ) * opN T ^ 2 := by
      rw [mul_pow, sq_sqrt (by positivity)]
      ring
    have hc : 0 ≤ opN T * sqrt (n : ℝ) := mul_nonneg (opN_nonneg _) (sqrt_nonneg _)
    nlinarith
  obtain ⟨hiY, hbY⟩ := gaussConc_moment (opN_nonneg T) hL P
  rw [← gaussMomConst_pow hP, ← mul_pow] at hbY
  have h := moment_shift hm ((hm.sub_const _).max measurable_const)
    (fun _ => nrm_nonneg _) (fun _ => le_max_right _ _)
    (mul_nonneg (opN_nonneg _) (sqrt_nonneg _))
    (fun w => by have hh := le_max_left (nrm (T *ᵥ w) -
      ∫ z, nrm (T *ᵥ z) ∂stdGauss (Fin m)) 0; linarith) hP
    (mul_nonneg (opN_nonneg _) (gaussMomConst_nonneg P)) hiY hbY
  simpa only [mul_add] using h

end BstLean.Part209
