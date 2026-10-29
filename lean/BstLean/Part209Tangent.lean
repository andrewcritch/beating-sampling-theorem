import BstLean.Part209Active
import BstLean.Part209Contraction
import BstLean.Part209MomentTools

/-! The sharp first-layer tangent-operator moment from the active count. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask)

variable {n m : ℕ}

lemma tangent_op_eq (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    opN (firstTangent A x) =
      opN (Matrix.diagonal (fun i => mask ((A *ᵥ x) i)) * (A * projT x)) := by
  rw [firstTangent_eq_tanB, opN_transpose]
  unfold tanB
  rw [Matrix.mul_assoc]

lemma measurable_tangent_op (x : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => opN (firstTangent A x)) := by
  simp_rw [tangent_op_eq]
  have hG : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A)) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).measurable.prodMk measurable_id
  have hD := (measurable_diag_mask_mul (p := m) (projT x)).comp hG
  exact opN_continuous.measurable.comp hD

theorem tangent_op_lintegral {P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P)
    {x : Fin n → ℝ} (hx : normSq x = 1) {v : ℝ} (hv : 0 < v) :
    (∫⁻ A : Matrix (Fin (n ^ 2)) (Fin n) ℝ, ENNReal.ofReal (opN (firstTangent A x) ^ (4 * P))
      ∂gaussMat (n ^ 2) n v) ≤
      ENNReal.ofReal ((sqrt v * (sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) +
        sqrt (n : ℝ) + gaussMomConst (2 * P))) ^ (4 * P)) := by
  let Φ : (Fin (n ^ 2) → ℝ) × Matrix (Fin (n ^ 2)) (Fin n) ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (opN (Matrix.diagonal (fun i => mask (z.1 i)) * z.2) ^ (4 * P))
  have hΦ : Measurable Φ := by
    have hm : Measurable (fun z : (Fin (n ^ 2) → ℝ) × Matrix (Fin (n ^ 2)) (Fin n) ℝ =>
        Matrix.diagonal (fun i => mask (z.1 i)) * z.2) := by
      simpa only [Matrix.mul_one] using measurable_diag_mask_mul (1 : Matrix (Fin n) (Fin n) ℝ)
    exact ((opN_continuous.measurable.comp hm).pow_const _).ennreal_ofReal
  simp_rw [tangent_op_eq]
  change (∫⁻ A, Φ (A *ᵥ x, A * projT x) ∂gaussMat (n ^ 2) n v) ≤ _
  rw [gaussMat_decomp hx hv.le hΦ]
  have hi : ∀ g : Fin (n ^ 2) → ℝ,
      (∫⁻ M, Φ (sqrt v • g, M * projT x) ∂gaussMat (n ^ 2) n v) ≤
      ENNReal.ofReal ((sqrt v * (sqrt (∑ i, mask (g i)) +
        sqrt (n : ℝ) + gaussMomConst (2 * P))) ^ (4 * P)) := by
    intro g
    have h := opN_rowsel_moment (fun i => mask (g i))
      (by intro i; unfold mask; split_ifs <;> simp) (projT x) hv.le (by omega : 1 ≤ 2 * P)
    simp only [show 2 * (2 * P) = 4 * P by omega] at h
    have hm : (fun i => mask ((sqrt v • g) i)) = fun i => mask (g i) := by
      funext i
      exact mask_mul_pos (sqrt_pos.mpr hv) _
    dsimp only [Φ]
    rw [hm]
    refine h.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (mul_nonneg (opN_nonneg _) (mul_nonneg (sqrt_nonneg _)
        (add_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (gaussMomConst_nonneg _)))) ?_ _))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (opN_projT_le hx)
      (mul_nonneg (sqrt_nonneg _) (add_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
        (gaussMomConst_nonneg (2 * P))))
  refine (lintegral_mono hi).trans ?_
  obtain ⟨hI, hB⟩ := active_sqrt_shift_moment hn hP
    (add_nonneg (sqrt_nonneg (n : ℝ)) (gaussMomConst_nonneg (2 * P)))
  have hI' : Integrable (fun g : Fin (n ^ 2) → ℝ =>
      (sqrt v * (sqrt (∑ i, mask (g i)) + (sqrt (n : ℝ) + gaussMomConst (2 * P)))) ^ (4 * P))
      (stdGauss (Fin (n ^ 2))) := by
    simp_rw [mul_pow]
    exact hI.const_mul _
  have hB' : (∫ g : Fin (n ^ 2) → ℝ,
      (sqrt v * (sqrt (∑ i, mask (g i)) + (sqrt (n : ℝ) + gaussMomConst (2 * P)))) ^ (4 * P)
      ∂stdGauss (Fin (n ^ 2))) ≤
      (sqrt v * (sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) +
        (sqrt (n : ℝ) + gaussMomConst (2 * P)))) ^ (4 * P) := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have h := lintegral_ofReal_le_of_integral_le (fun g => pow_nonneg
    (mul_nonneg (sqrt_nonneg _) (add_nonneg (sqrt_nonneg _)
      (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _)))) _) hI' hB'
  simpa only [add_assoc] using h

noncomputable def tangentRoot (n P : ℕ) : ℝ :=
  sqrt 2 / (n : ℝ) * (sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) +
    sqrt (n : ℝ) + gaussMomConst (2 * P))

noncomputable def tangentU (n P : ℕ) : ℝ :=
  2 / (n : ℝ) ^ 2 * (sqrt ((n : ℝ) ^ 2 / 2 + activeB n P) +
    sqrt (n : ℝ) + gaussMomConst (2 * P)) ^ 2

lemma tangentRoot_nonneg (n P : ℕ) : 0 ≤ tangentRoot n P :=
  mul_nonneg (by positivity) (add_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    (gaussMomConst_nonneg _))

lemma tangentRoot_sq (n P : ℕ) : tangentRoot n P ^ 2 = tangentU n P := by
  unfold tangentRoot tangentU
  rw [mul_pow, div_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma tangentRoot_eq_sqrt (n P : ℕ) : tangentRoot n P = sqrt (tangentU n P) := by
  rw [← tangentRoot_sq, sqrt_sq (tangentRoot_nonneg n P)]

/-- This is the paper operator allowance `U_(4P)`, with the actual first-layer distribution. -/
theorem tangent_op_moment_paper {P : ℕ} (hn : 1 ≤ n) (hP : 1 ≤ P)
    {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ =>
      (opN (firstTangent A x) / sqrt (n : ℝ)) ^ (4 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, (opN (firstTangent A x) / sqrt (n : ℝ)) ^ (4 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      sqrt (tangentU n P) ^ (4 * P) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := tangent_op_lintegral hn hP hx (by positivity : 0 < 2 / (n : ℝ))
  simp_rw [ENNReal.ofReal_pow (opN_nonneg _)] at hb
  obtain ⟨hi, hm⟩ := moment_of_lintegral (measurable_tangent_op (m := n ^ 2) x)
    (fun _ => opN_nonneg _) (mul_nonneg (sqrt_nonneg _)
      (add_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (gaussMomConst_nonneg _))) hb
  simp_rw [div_pow]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  refine (div_le_div_of_nonneg_right hm (by positivity)).trans_eq ?_
  rw [← div_pow, ← tangentRoot_eq_sqrt]
  congr 1
  have hs : sqrt (2 / (n : ℝ)) / sqrt (n : ℝ) = sqrt 2 / (n : ℝ) := by
    rw [sqrt_div (by norm_num), div_div, mul_self_sqrt hn0.le]
  unfold tangentRoot
  rw [mul_div_right_comm, hs]

end BstLean.Part209
