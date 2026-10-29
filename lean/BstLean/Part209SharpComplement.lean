import BstLean.Part209Tangent
import BstLean.Part209Complement
import BstLean.Part209Delta

/-! The sharp low-length complement for the actual conditional mean. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

variable {n P : ℕ}

theorem layerLength_upper_moment (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun A => layerLength A x ^ (2 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, layerLength A x ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      (1 + lengthAlpha n P) ^ (2 * P) := by
  obtain ⟨hi, hb⟩ := layerLength_deviation_moment hn hP hx
  exact moment_shift (measurable_layerLength x) ((measurable_layerLength x).sub_const 1).abs
    (fun A => layerLength_nonneg A x) (fun _ => abs_nonneg _) zero_le_one
    (fun A => by have := le_abs_self (layerLength A x - 1); linarith)
    hP (lengthAlpha_nonneg n P) hi hb

lemma meanError_product_le (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    meanError x x' A ≤ 1 + (opN (firstTangent A x) / sqrt (n : ℝ)) * layerLength A x' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := nrm_sub_le ((n : ℝ)⁻¹ • pairMean (p := n ^ 2) (2 / (n ^ 2 : ℕ)) A x x')
    (pairIdeal x x')
  rw [nrm_smul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)] at h
  have hb := mul_le_mul_of_nonneg_left (pairMean_he_le (p := n ^ 2) (one_le_pow₀ hn) A x x')
    (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  have he : (n : ℝ)⁻¹ * (opN (firstTangent A x) * nrm (reluV (A *ᵥ x'))) =
      (opN (firstTangent A x) / sqrt (n : ℝ)) * layerLength A x' := by
    rw [layerLength_eq hn, div_mul_div_comm, mul_self_sqrt hn0.le]
    ring
  rw [he] at hb
  have hid := pairIdeal_le hx hx'
  change nrm _ ≤ _
  linarith

noncomputable def complementRoot (n P : ℕ) : ℝ :=
  sqrt (tangentU n (4 * P)) * (1 + lengthAlpha n (8 * P)) + 1

lemma complementRoot_nonneg (n P : ℕ) : 0 ≤ complementRoot n P :=
  add_nonneg (mul_nonneg (sqrt_nonneg _) (add_nonneg zero_le_one (lengthAlpha_nonneg _ _))) zero_le_one

theorem meanError_sharp_high_moment (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun A => meanError x x' A ^ (8 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, meanError x x' A ^ (8 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      complementRoot n P ^ (8 * P) := by
  let T := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => opN (firstTangent A x) / sqrt (n : ℝ)
  let L := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => layerLength A x'
  have hT : Measurable T := (measurable_tangent_op x).div_const _
  have hL : Measurable L := measurable_layerLength x'
  have hT0 : ∀ A, 0 ≤ T A := fun A => div_nonneg (opN_nonneg _) (sqrt_nonneg _)
  have hL0 : ∀ A, 0 ≤ L A := fun A => layerLength_nonneg A x'
  obtain ⟨hiT, hbT⟩ := tangent_op_moment_paper (by omega : 1 ≤ n) (by omega : 1 ≤ 4 * P) hx
  obtain ⟨hiL, hbL⟩ := layerLength_upper_moment hn (by omega : 1 ≤ 8 * P) hx'
  have he : 4 * (4 * P) = 2 * (8 * P) := by omega
  rw [he] at hiT hbT
  obtain ⟨hiY, hbY⟩ := moment_mul hT hL hT0 hL0 (sqrt_nonneg _)
    (add_nonneg zero_le_one (lengthAlpha_nonneg n (8 * P))) hiT hiL hbT hbL
  have h := moment_shift (measurable_meanError x x') (hT.mul hL)
    (fun _ => nrm_nonneg _) (fun A => mul_nonneg (hT0 A) (hL0 A)) zero_le_one
    (fun A => meanError_product_le (by omega) hx hx' A)
    (show 1 ≤ 4 * P by omega)
    (mul_nonneg (sqrt_nonneg _) (add_nonneg zero_le_one (lengthAlpha_nonneg n (8 * P))))
    (by simpa only [show 2 * (4 * P) = 8 * P by omega, Pi.mul_apply] using hiY)
    (by simpa only [show 2 * (4 * P) = 8 * P by omega, Pi.mul_apply] using hbY)
  simpa only [show 2 * (4 * P) = 8 * P by omega, complementRoot, add_comm] using h

noncomputable def lowLengthProb (n : ℕ) (η : ℝ) : ℝ :=
  4 * exp (-(n : ℝ) ^ 2 * (η - 2 / (n : ℝ) ^ 2) ^ 2 / 4)

noncomputable def complementB (n P : ℕ) (η : ℝ) : ℝ :=
  complementRoot n P * lowLengthProb n η ^ (1 / (8 * (P : ℝ)))

/-- This is the paper `B_(4P)` allowance. The bad set is integrated once. -/
theorem meanError_sharp_lowLength (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    (∫ A in {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|},
      meanError x x' A ^ (4 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤ complementB n P η ^ (4 * P) := by
  have hB : MeasurableSet {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|} :=
    (measurableSet_lt measurable_const ((measurable_layerLength x).sub_const 1).abs).union
      (measurableSet_lt measurable_const ((measurable_layerLength x').sub_const 1).abs)
  obtain ⟨hi, hb⟩ := meanError_sharp_high_moment hn hP hx hx'
  have he : 8 * P = 2 * (4 * P) := by omega
  rw [he] at hi hb
  have h := restricted_moment_bound (measurable_meanError x x') (fun _ => nrm_nonneg _) hi hB hb
    (pair_lowLength_probability hn hx hx' hη)
  refine h.trans_eq ?_
  rw [Nat.mul_comm 2 (4 * P), pow_mul, sqrt_sq (pow_nonneg (complementRoot_nonneg n P) _)]
  unfold complementB
  rw [mul_pow]
  congr 1
  have hp0 : (P : ℝ) ≠ 0 := by positivity
  have hprob : 0 ≤ lowLengthProb n η := by unfold lowLengthProb; positivity
  rw [← rpow_natCast (lowLengthProb n η ^ (1 / (8 * (P : ℝ)))) (4 * P),
    ← rpow_mul hprob]
  have hex : 1 / (8 * (P : ℝ)) * ((4 * P : ℕ) : ℝ) = 1 / 2 := by
    push_cast
    field_simp
    norm_num
  rw [hex, ← sqrt_eq_rpow]
  rfl

end BstLean.Part209
