import BstLean.Part209PairMoments

/-! The four sharp terms for the conditional-mean error. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
variable {n P : ℕ}

noncomputable def badMean (x x' : Fin n → ℝ) (η : ℝ) :
    Matrix (Fin (n ^ 2)) (Fin n) ℝ → ℝ :=
  (goodLength x x' η)ᶜ.indicator (meanError x x')

lemma measurable_badMean (x x' : Fin n → ℝ) (η : ℝ) : Measurable (badMean x x' η) :=
  (measurable_meanError x x').indicator (measurableSet_goodLength x x' η).compl

lemma badMean_nonneg (x x' : Fin n → ℝ) (η : ℝ) (A) : 0 ≤ badMean x x' η A :=
  indicator_nonneg (fun _ _ => nrm_nonneg _) _

noncomputable def radialError (x : Fin n → ℝ) (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) : ℝ :=
  nrm ((n : ℝ)⁻¹ • firstPair A x x)

lemma measurable_radialError (x : Fin n → ℝ) : Measurable (radialError x) :=
  (BstLean.Part130.measurable_normSq.comp
    ((measurable_firstPair_self x).const_smul ((n : ℝ)⁻¹))).sqrt

noncomputable def radialCoefficient (η : ℝ) : ℝ := (1 + η) / (π * (1 - η))

lemma radialCoefficient_nonneg {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1) :
    0 ≤ radialCoefficient η := by unfold radialCoefficient; positivity

lemma meanError_four_terms (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η < 1)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    meanError x x' A ≤ firstPairError x x' A + 3 / 10 * sqrt (goodCorrelation x x' η A) +
      radialCoefficient η * radialError x A + badMean x x' η A := by
  classical
  by_cases hA : A ∈ goodLength x x' η
  · have hL : 1 - η ≤ layerLength A x := by have := (abs_le.mp hA.1).1; linarith
    have hR : layerLength A x' ≤ 1 + η := by have := (abs_le.mp hA.2).2; linarith
    have hLp : 0 < layerLength A x := by linarith
    have ha : reluV (A *ᵥ x) ≠ 0 := by
      intro ha
      rw [layerLength_eq hn, ha] at hLp
      simpa [nrm, normSq] using hLp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hna : nrm (reluV (A *ᵥ x)) ≠ 0 := fun h => ha (nrm_eq_zero' h)
    have he : nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) = layerLength A x' / layerLength A x := by
      rw [layerLength_eq hn, layerLength_eq hn]
      field_simp
    have hratio : layerLength A x' / layerLength A x ≤ (1 + η) / (1 - η) := by
      apply (div_le_iff₀ hLp).mpr
      have h := mul_le_mul_of_nonneg_left hL
        (div_nonneg (by linarith : 0 ≤ 1 + η) (by linarith : 0 ≤ 1 - η))
      rw [div_mul_cancel₀ _ (by linarith : 1 - η ≠ 0)] at h
      exact hR.trans h
    have hc : nrm (reluV (A *ᵥ x')) / nrm (reluV (A *ᵥ x)) / π ≤ radialCoefficient η := by
      rw [he]
      have h := div_le_div_of_nonneg_right hratio pi_pos.le
      refine h.trans_eq ?_
      unfold radialCoefficient
      rw [div_div, mul_comm (1 - η) π]
    have h := pairMean_comparison (p := n ^ 2) (one_le_pow₀ hn) A hx hx' ha ((n : ℝ)⁻¹)
    have hr := mul_le_mul_of_nonneg_right hc (nrm_nonneg ((n : ℝ)⁻¹ • firstPair A x x))
    rw [goodCorrelation, indicator_of_mem hA, badMean,
      indicator_of_notMem (show A ∉ (goodLength x x' η)ᶜ from fun hh => hh hA), add_zero]
    exact h.trans (by dsimp [firstPairError, radialError]; linarith)
  · rw [badMean, indicator_of_mem hA]
    have hF : 0 ≤ firstPairError x x' A := nrm_nonneg _
    have hR := mul_nonneg (radialCoefficient_nonneg hη0 hη) (nrm_nonneg ((n : ℝ)⁻¹ • firstPair A x x))
    have hC : 0 ≤ 3 / 10 * sqrt (goodCorrelation x x' η A) := by positivity
    dsimp [radialError] at *
    linarith

theorem badMean_moment (hn : 2 ≤ n) (hP : 1 ≤ P) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ} (hη : 2 / (n : ℝ) ^ 2 ≤ η) :
    Integrable (fun A => badMean x x' η A ^ (4 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, badMean x x' η A ^ (4 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤ complementB n P η ^ (4 * P) := by
  classical
  have he : (fun A => badMean x x' η A ^ (4 * P)) =
      (goodLength x x' η)ᶜ.indicator (fun A => meanError x x' A ^ (4 * P)) := by
    ext A
    by_cases hA : A ∈ (goodLength x x' η)ᶜ <;> simp [badMean, hA, show 4 * P ≠ 0 by omega]
  have hs : (goodLength x x' η)ᶜ =
      {A | η < |layerLength A x - 1| ∨ η < |layerLength A x' - 1|} := by
    ext A
    simp only [mem_compl_iff, goodLength, mem_setOf_eq, not_and_or, not_le]
  rw [he]
  refine ⟨(meanError_moment (by omega) (s := 4 * P) (by omega) hx hx').1.indicator
    (measurableSet_goodLength x x' η).compl, ?_⟩
  rw [integral_indicator (measurableSet_goodLength x x' η).compl, hs]
  exact meanError_sharp_lowLength hn hP hx hx' hη

noncomputable def meanEpsilon (n P : ℕ) (η : ℝ) : ℝ :=
  pairV n (2 * P) + 3 / 10 * sqrt (pairDelta n P η) +
    radialCoefficient η * pairQ n (2 * P) + complementB n P η

theorem meanError_sharp_moment (hn : 2 ≤ n) (hP : 1 ≤ P) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) {η : ℝ}
    (hη0 : 2 / (n : ℝ) ^ 2 ≤ η) (hη : η < 1) :
    Integrable (fun A => meanError x x' A ^ (4 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, meanError x x' A ^ (4 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤ meanEpsilon n P η ^ (4 * P) := by
  have he : 2 * (2 * P) = 4 * P := by omega
  have hηn : 0 ≤ η := (by positivity : 0 ≤ 2 / (n : ℝ) ^ 2).trans hη0
  have hc := radialCoefficient_nonneg hηn hη
  have hq : 0 ≤ pairQ n (2 * P) := pairQ_nonneg _ _
  have hb0 : 0 ≤ complementB n P η := mul_nonneg (complementRoot_nonneg _ _)
    (Real.rpow_nonneg (by unfold lowLengthProb; positivity) _)
  obtain ⟨hiF, hbF⟩ := firstPairError_moment (by omega) (by omega : 1 ≤ 2 * P) hx hx'
  rw [he] at hiF hbF
  obtain ⟨hiC, hbC⟩ := sqrt_goodCorrelation_moment hn hP hx hx' hη
  obtain ⟨hiC, hbC⟩ := moment_const_mul (by norm_num : (0 : ℝ) ≤ 3 / 10) hiC hbC
  obtain ⟨hiR, hbR⟩ := radialPair_moment_paper (by omega : 1 ≤ n) (by omega : 1 ≤ 2 * P) hx
  rw [he] at hiR hbR
  obtain ⟨hiR, hbR⟩ := moment_const_mul hc hiR hbR
  obtain ⟨hiB, hbB⟩ := badMean_moment hn hP hx hx' hη0
  have hF := measurable_firstPairError x x'
  have hC := ((measurable_goodCorrelation (by omega) x x' η).sqrt).const_mul (3 / 10 : ℝ)
  have hR := (measurable_radialError x).const_mul (radialCoefficient η)
  have hB := measurable_badMean x x' η
  have hF0 : ∀ A, 0 ≤ firstPairError x x' A := fun _ => nrm_nonneg _
  have hC0 : ∀ A, 0 ≤ 3 / 10 * sqrt (goodCorrelation x x' η A) := fun _ => by positivity
  have hR0 : ∀ A, 0 ≤ radialCoefficient η * radialError x A :=
    fun _ => mul_nonneg hc (nrm_nonneg _)
  have hfc : 0 ≤ pairV n (2 * P) + 3 / 10 * sqrt (pairDelta n P η) :=
    add_nonneg (pairV_nonneg n (2 * P)) (mul_nonneg (by norm_num) (sqrt_nonneg _))
  obtain ⟨hiFC, hbFC⟩ := moment_add hF hC hF0 hC0 (by omega : 1 ≤ 4 * P)
    (pairV_nonneg _ _) (mul_nonneg (by norm_num) (sqrt_nonneg _)) hiF hiC hbF hbC
  obtain ⟨hiFCR, hbFCR⟩ := moment_add (hF.add hC) hR (fun A => add_nonneg (hF0 A) (hC0 A)) hR0
    (by omega : 1 ≤ 4 * P) hfc (mul_nonneg hc hq) hiFC hiR hbFC hbR
  obtain ⟨hiAll, hbAll⟩ := moment_add ((hF.add hC).add hR) hB
    (fun A => add_nonneg (add_nonneg (hF0 A) (hC0 A)) (hR0 A)) (badMean_nonneg x x' η)
    (by omega : 1 ≤ 4 * P) (add_nonneg hfc (mul_nonneg hc hq)) hb0 hiFCR hiB hbFCR hbB
  exact moment_mono (measurable_meanError x x') (fun _ => nrm_nonneg _)
    (meanError_four_terms (by omega) hx hx' hηn hη) hiAll hbAll

end BstLean.Part209
