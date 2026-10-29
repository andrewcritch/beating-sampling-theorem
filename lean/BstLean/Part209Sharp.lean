import BstLean.Part209MeanMoment

/-! The fixed-pair derivative error has the paper epsilon, with no exceptional event. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
variable {n P : ℕ}

lemma measurable_fluctuation (x x' : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin (n ^ 2)) (Fin n) ℝ ×
      Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ => fluctuation x x' θ.1 θ.2) := by
  exact (BstLean.Part130.measurable_normSq.comp
    (((measurable_pairVector x x').sub ((measurable_pairMean _ x x').comp measurable_fst)).const_smul
      ((n : ℝ)⁻¹))).sqrt

noncomputable def fluctuationRoot (n P : ℕ) : ℝ :=
  pairV n (2 * P) * sqrt (tangentU n (2 * P)) * (1 + lengthAlpha n (4 * P))

lemma fluctuationRoot_nonneg (n P : ℕ) : 0 ≤ fluctuationRoot n P :=
  mul_nonneg (mul_nonneg (pairV_nonneg _ _) (sqrt_nonneg _))
    (add_nonneg zero_le_one (lengthAlpha_nonneg _ _))

theorem fluctuation_joint_moment (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun θ => fluctuation x x' θ.1 θ.2 ^ (4 * P)) (nuA n) ∧
    (∫ θ, fluctuation x x' θ.1 θ.2 ^ (4 * P) ∂nuA n) ≤ fluctuationRoot n P ^ (4 * P) := by
  let T := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => opN (firstTangent A x) / sqrt (n : ℝ)
  let L := fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => layerLength A x'
  have hT : Measurable T := (measurable_tangent_op x).div_const _
  have hL : Measurable L := measurable_layerLength x'
  have hT0 : ∀ A, 0 ≤ T A := fun A => div_nonneg (opN_nonneg _) (sqrt_nonneg _)
  have hL0 : ∀ A, 0 ≤ L A := fun A => layerLength_nonneg A x'
  obtain ⟨hiT, hbT⟩ := tangent_op_moment_paper (by omega : 1 ≤ n) (by omega : 1 ≤ 2 * P) hx
  obtain ⟨hiL, hbL⟩ := layerLength_upper_moment hn (by omega : 1 ≤ 4 * P) hx'
  have he : 4 * (2 * P) = 2 * (4 * P) := by omega
  rw [he] at hiT hbT
  obtain ⟨hi, hb⟩ := moment_mul hT hL hT0 hL0 (sqrt_nonneg _)
    (add_nonneg zero_le_one (lengthAlpha_nonneg n (4 * P))) hiT hiL hbT hbL
  obtain ⟨hi, hb⟩ := moment_const_mul (pairV_nonneg n (2 * P)) hi hb
  have hlin := lintegral_of_moment (fun A => mul_nonneg (pairV_nonneg n (2 * P))
    (mul_nonneg (hT0 A) (hL0 A))) hi hb
  apply moment_of_lintegral (measurable_fluctuation x x') (fun _ => nrm_nonneg _)
    (fluctuationRoot_nonneg n P)
  change (∫⁻ θ : Matrix (Fin (n ^ 2)) (Fin n) ℝ ×
      Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ,
      ENNReal.ofReal (fluctuation x x' θ.1 θ.2) ^ (4 * P)
        ∂(gaussMat (n ^ 2) n (2 / n)).prod
          (gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ)))) ≤
    ENNReal.ofReal (fluctuationRoot n P ^ (4 * P))
  rw [lintegral_prod _ ((measurable_fluctuation x x').ennreal_ofReal.pow_const _).aemeasurable]
  have hpoint : ∀ A : Matrix (Fin (n ^ 2)) (Fin n) ℝ,
      (∫⁻ B, ENNReal.ofReal (fluctuation x x' A B) ^ (4 * P)
        ∂gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ))) ≤
      ENNReal.ofReal (pairV n (2 * P) * (T A * L A)) ^ (4 * P) := by
    intro A
    obtain ⟨hI, hB⟩ := fluctuation_conditional_moment (by omega : 1 ≤ n)
      (by omega : 1 ≤ 2 * P) x x' A
    have h := lintegral_of_moment (fun B => nrm_nonneg _) hI hB
    rw [show 2 * (2 * P) = 4 * P by omega] at h
    rw [← ENNReal.ofReal_pow (mul_nonneg (pairV_nonneg n (2 * P)) (mul_nonneg (hT0 A) (hL0 A)))]
    simpa only [T, L, mul_assoc, fluctuation] using h
  refine (lintegral_mono hpoint).trans (hlin.trans_eq ?_)
  unfold fluctuationRoot
  congr 2
  ring

noncomputable def pairEpsilon (n P : ℕ) (η : ℝ) : ℝ :=
  meanEpsilon n P η + fluctuationRoot n P

lemma meanEpsilon_nonneg (n P : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1) :
    0 ≤ meanEpsilon n P η := by
  unfold meanEpsilon
  apply add_nonneg
  · apply add_nonneg
    · exact add_nonneg (pairV_nonneg _ _) (mul_nonneg (by norm_num) (sqrt_nonneg _))
    · exact mul_nonneg (radialCoefficient_nonneg hη0 hη) (pairQ_nonneg _ _)
  · exact mul_nonneg (complementRoot_nonneg _ _)
      (Real.rpow_nonneg (by unfold lowLengthProb; positivity) _)

theorem paperPairError_sharp_moment_general (hn : 2 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    {η : ℝ} (hη0 : 2 / (n : ℝ) ^ 2 ≤ η) (hη : η < 1) :
    Integrable (fun θ => paperPairError x x' θ ^ (4 * P)) (nuA n) ∧
    (∫ θ, paperPairError x x' θ ^ (4 * P) ∂nuA n) ≤ pairEpsilon n P η ^ (4 * P) := by
  have hηn : 0 ≤ η := (by positivity : 0 ≤ 2 / (n : ℝ) ^ 2).trans hη0
  obtain ⟨hiF, hbF⟩ := fluctuation_joint_moment hn hP hx hx'
  obtain ⟨hiM, hbM⟩ := meanError_sharp_moment hn hP hx hx' hη0 hη
  have hiM' := hiM.comp_fst (gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ)))
  have hbM' : (∫ θ, meanError x x' θ.1 ^ (4 * P) ∂nuA n) ≤ meanEpsilon n P η ^ (4 * P) := by
    change (∫ θ : Matrix (Fin (n ^ 2)) (Fin n) ℝ ×
        Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ,
        meanError x x' θ.1 ^ (4 * P)
          ∂(gaussMat (n ^ 2) n (2 / n)).prod
            (gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ)))) ≤ meanEpsilon n P η ^ (4 * P)
    have he := integral_fun_fst (μ := gaussMat (n ^ 2) n (2 / n))
      (ν := gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ)))
      (fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ => meanError x x' A ^ (4 * P))
    simp only [probReal_univ, one_smul] at he
    exact he.trans_le hbM
  obtain ⟨hi, hb⟩ := moment_add ((measurable_meanError x x').comp measurable_fst)
    (measurable_fluctuation x x') (fun _ => nrm_nonneg _) (fun _ => nrm_nonneg _)
    (by omega : 1 ≤ 4 * P) (meanEpsilon_nonneg n P hηn hη) (fluctuationRoot_nonneg n P)
    hiM' hiF hbM' hbF
  apply moment_mono (measurable_paperPairError x x') (paperPairError_nonneg x x') _ hi hb
  intro θ
  have he : (n : ℝ)⁻¹ • pairVector θ.1 θ.2 x x' - pairIdeal x x' =
      ((n : ℝ)⁻¹ • pairMean (p := n ^ 2) (2 / (n ^ 2 : ℕ)) θ.1 x x' - pairIdeal x x') +
        (n : ℝ)⁻¹ • (pairVector θ.1 θ.2 x x' -
          pairMean (p := n ^ 2) (2 / (n ^ 2 : ℕ)) θ.1 x x') := by module
  change nrm _ ≤ _
  rw [he]
  exact nrm_add_le _ _

/-- This is the paper fixed-pair bound at every positive order divisible by four.
The threshold `n >= 15` makes the one-percent length cutoff admissible. -/
theorem paperPairError_sharp_moment (hn : 15 ≤ n) (hP : 1 ≤ P)
    {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun θ => paperPairError x x' θ ^ (4 * P)) (nuA n) ∧
    (∫ θ, paperPairError x x' θ ^ (4 * P) ∂nuA n) ≤ pairEpsilon n P (1 / 100) ^ (4 * P) := by
  apply paperPairError_sharp_moment_general (by omega) hP hx hx' _ (by norm_num)
  have hnR : (15 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [div_le_iff₀ (pow_pos hn0 2)]
  nlinarith

end BstLean.Part209
