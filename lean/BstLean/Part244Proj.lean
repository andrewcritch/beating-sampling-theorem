import BstLean.Part244RowGram
import BstLean.Part182EBlk4

/-! Part 244: the projection tail of the sharp E block (paper table: "Projection of `A₂|V_E`
onto `S₂A₂(U₂)`"). The rank-two projection is chosen from `A·P`; the Gaussian part `A·U` is
independent because `P U = 0`. -/
namespace BstLean.Part244
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg gaussMat)
open BstLean.Part152 (opN opN_nonneg opN_continuous)
open BstLean.Part182 (e4_Q e4_measurable_Q e4_Q_rk2 e4_proj_tail eb_rot eb_colsplit e2_mulU_eq)

/-- The rank-two projection tail at a fixed left factor. -/
lemma fixed_proj_tail {M k D : ℕ} {v υ : ℝ} (hv : 0 < v) (hυ : 0 ≤ υ) (z₁ z₂ : Fin M → ℝ)
    (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) :
    (gaussMat M k v) {A | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q z₁ z₂ * (A * U))} ≤
      ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
  obtain ⟨r, hr, W, hW, hQW, hQ1⟩ := e4_Q_rk2 z₁ z₂
  have hυ2 : √(2 * (υ ^ 2 / 2)) = υ := by
    rw [show 2 * (υ ^ 2 / 2) = υ ^ 2 by ring, Real.sqrt_sq hυ]
  have h := e4_proj_tail (m := M) (n := D) hv (e4_Q z₁ z₂) hr W hW hQW hQ1
    (1 : Matrix (Fin D) (Fin D) ℝ) (by
      refine BstLean.Part153.opN_le_of_bound _ zero_le_one fun w => ?_
      simp) (τ := υ ^ 2 / 2) (by positivity)
  rw [hυ2, show -(υ ^ 2 / 2) = -υ ^ 2 / 2 by ring] at h
  have hf : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * U) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hmap : (gaussMat M k v).map (fun A => A * U) = gaussMat M D v := by
    have h := eb_rot (M := M) (k := k) (K := M) (d := D) hv.le
      (1 : Matrix (Fin M) (Fin M) ℝ) U (by simp) hU
    simpa using h
  calc (gaussMat M k v) {A | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q z₁ z₂ * (A * U))}
      = (gaussMat M k v) ((fun A => A * U) ⁻¹'
          {G | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q z₁ z₂ * (G * (1 : Matrix (Fin D) (Fin D) ℝ)))}) := by
        congr 1; ext A; simp only [Set.mem_preimage, Set.mem_setOf_eq, Matrix.mul_one]
    _ ≤ ((gaussMat M k v).map (fun A => A * U))
          {G | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q z₁ z₂ * (G * (1 : Matrix (Fin D) (Fin D) ℝ)))} :=
        Measure.le_map_apply hf.aemeasurable _
    _ = _ := by rw [hmap]
    _ ≤ _ := h

/-- **Conditional projection tail.** If the two spanning vectors depend only on `A·P` and
`P U = 0`, the rank-two projection of `A U` exceeds `√v (√2 + √D + υ)` with probability at most
`e^{-υ²/2}`. -/
theorem split_proj_tail {M k D : ℕ} {v υ : ℝ} (hv : 0 < v) (hυ : 0 ≤ υ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P)
    (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) (hPU : P * U = 0)
    (zF : Matrix (Fin M) (Fin k) ℝ → (Fin M → ℝ) × (Fin M → ℝ)) (hzF : Measurable zF) :
    (gaussMat M k v) {A | √v * (√2 + √(D : ℝ) + υ) ≤
      opN (e4_Q (zF (A * P)).1 (zF (A * P)).2 * (A * U))} ≤ ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
  classical
  haveI : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  have hg1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg2 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) :=
    hg1.prodMk hg2
  set S : Set (Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ) :=
    {q | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q (zF q.1).1 (zF q.1).2 * (q.2 * U))} with hSd
  have hSm : MeasurableSet S := by
    have hQm : Measurable (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        e4_Q (zF q.1).1 (zF q.1).2) := e4_measurable_Q.comp (hzF.comp measurable_fst)
    have hc : Continuous (fun z : Matrix (Fin M) (Fin M) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        z.1 * (z.2 * U)) := continuous_fst.matrix_mul (continuous_snd.matrix_mul continuous_const)
    have h2 := hc.measurable.comp (hQm.prodMk measurable_snd)
    exact measurableSet_le measurable_const (opN_continuous.measurable.comp h2)
  have e : {A : Matrix (Fin M) (Fin k) ℝ | √v * (√2 + √(D : ℝ) + υ) ≤
      opN (e4_Q (zF (A * P)).1 (zF (A * P)).2 * (A * U))} =
      (fun A => (A * P, A * (1 - P))) ⁻¹' S := by
    ext A
    simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, e2_mulU_eq P U hPU]
  rw [e, ← Measure.map_apply hg hSm, eb_colsplit v P hPs hPi]
  set μ₁ := (gaussMat M k v).map (fun A => A * P)
  set μ₂ := (gaussMat M k v).map (fun A => A * (1 - P))
  have : IsProbabilityMeasure μ₁ := inferInstance
  have : IsProbabilityMeasure μ₂ := inferInstance
  rw [Measure.prod_apply hSm]
  have hle : ∀ B, μ₂ (Prod.mk B ⁻¹' S) ≤ ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by
    intro B
    have hT : MeasurableSet (Prod.mk B ⁻¹' S) := measurable_prodMk_left hSm
    rw [Measure.map_apply hg2 hT]
    have e2 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) ⁻¹' (Prod.mk B ⁻¹' S) =
        {A | √v * (√2 + √(D : ℝ) + υ) ≤ opN (e4_Q (zF B).1 (zF B).2 * (A * U))} := by
      ext A; simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, e2_mulU_eq P U hPU]
    rw [e2]
    exact fixed_proj_tail hv hυ (zF B).1 (zF B).2 U hU
  calc ∫⁻ B, μ₂ (Prod.mk B ⁻¹' S) ∂μ₁ ≤ ∫⁻ _B, ENNReal.ofReal (exp (-υ ^ 2 / 2)) ∂μ₁ :=
        lintegral_mono hle
    _ = ENNReal.ofReal (exp (-υ ^ 2 / 2)) := by rw [lintegral_const, measure_univ, mul_one]

end BstLean.Part244
