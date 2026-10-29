import BstLean.Part246Gram
import BstLean.Part244RowGram

/-! Part 244: the row-selected centred Gram tail on a `D`-dimensional subspace, and its
conditional form when the row selection depends only on `A·P` with `P·U = 0`.
This is the singular-value step of the sharp E block: given `A₁` and `A₂|U₂`, the active rows of
`S₂ A₂ Q` restricted to `V_E` form a Gaussian matrix. -/
namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg gaussMat)
open BstLean.Part152 (opN opN_nonneg opN_continuous)
open BstLean.Part153 (nrm nrm_nonneg)
open BstLean.Part244 (gramDev dot_diag_sel gramDev_le_of_bil gramDev_mulU)

/-- The paper's Gram radius `2√K h + h²`, `h = √D + υ`. -/
noncomputable def gramRad (K D υ : ℝ) : ℝ :=
  2 * √K * (√D + υ) + (√D + υ) ^ 2

lemma gramRad_nonneg {K D υ : ℝ} (hυ : 0 ≤ υ) : 0 ≤ gramRad K D υ := by
  unfold gramRad; positivity

/-- **Row-selected Gram tail** for a fixed `{0,1}` selection and orthonormal columns `U`. -/
theorem rowsel_gram_tail {M k D : ℕ} (hD : 1 ≤ D) {v υ : ℝ} (hv : 0 < v) (hυ : 0 ≤ υ)
    (d : Fin M → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1) (U : Matrix (Fin k) (Fin D) ℝ)
    (hU : Uᵀ * U = 1) :
    (gaussMat M k v).real {A | v * gramRad (∑ i, d i) D υ < gramDev v d U A} ≤
      2 * exp (-υ ^ 2 / 2) := by
  classical
  haveI : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin M), ∀ i, i ∈ S ↔ d i = 1 :=
    ⟨Finset.univ.filter fun i => d i = 1, by simp⟩
  have hd' : ∀ i, d i = if i ∈ S then 1 else 0 := by
    intro i
    rcases hd i with h | h
    · have : i ∉ S := by rw [hS, h]; norm_num
      simp [this, h]
    · simp [(hS i).2 h, h]
  have hsum : ∑ i, d i = (S.card : ℝ) := by
    simp only [hd']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  obtain ⟨K', hK'⟩ : ∃ K', S.card = K' := ⟨_, rfl⟩
  rw [hsum, hK']
  have hexp0 : 0 ≤ 2 * exp (-υ ^ 2 / 2) := by positivity
  rcases Nat.eq_zero_or_pos K' with hK0 | hKpos
  · -- no active rows: the deviation is zero
    have hd0 : ∀ i, d i = 0 := by
      intro i
      rw [hd' i]
      have : i ∉ S := by
        intro hi
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      simp [this]
    have he : {A : Matrix (Fin M) (Fin k) ℝ | v * gramRad (K' : ℝ) D υ < gramDev v d U A} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro A hA
      have hdz : d = 0 := funext hd0
      have h0 : gramDev v d U A = 0 := by
        unfold gramDev
        rw [hdz]
        simp only [Matrix.diagonal_zero, Matrix.zero_mul, Matrix.mul_zero, Pi.zero_apply,
          Finset.sum_const_zero, mul_zero, zero_smul, sub_zero, transpose_zero]
        exact le_antisymm (BstLean.Part182.ms_opN_le_of_bil _ le_rfl fun p q => by simp)
          (opN_nonneg _)
      have := mul_nonneg hv.le (gramRad_nonneg (K := (K' : ℝ)) (D := D) hυ)
      simp only [mem_setOf_eq] at hA
      linarith
    rw [he, measureReal_empty]; exact hexp0
  · set σ := S.orderEmbOfFin hK' with hσ
    let f : Matrix (Fin M) (Fin k) ℝ → Matrix (Fin K') (Fin D) ℝ :=
      fun A => (A * U).submatrix σ id
    set Bad := {G : Matrix (Fin K') (Fin D) ℝ | ¬ ∀ p q : Fin D → ℝ,
      |(G *ᵥ p) ⬝ᵥ (G *ᵥ q) - v * K' * (p ⬝ᵥ q)| ≤
        v * (2 * √(K' : ℝ) * (√(D : ℝ) + υ) +
          (√(D : ℝ) + υ) ^ 2) * √(normSq p) * √(normSq q)} with hBad
    have hsub : {A : Matrix (Fin M) (Fin k) ℝ | v * gramRad (K' : ℝ) D υ < gramDev v d U A} ⊆
        f ⁻¹' Bad := by
      intro A hA hgood
      simp only [mem_setOf_eq] at hA
      have hle : gramDev v d U A ≤ v * gramRad (K' : ℝ) D υ := by
        unfold gramDev
        rw [hsum, hK']
        refine gramDev_le_of_bil (mul_nonneg hv.le (gramRad_nonneg hυ)) fun p q => ?_
        have e : p ⬝ᵥ ((Matrix.diagonal d * (A * U))ᵀ * (Matrix.diagonal d * (A * U))) *ᵥ q =
            (f A *ᵥ p) ⬝ᵥ (f A *ᵥ q) := by
          rw [← BstLean.Part182.ms_bil]
          rw [show (Matrix.diagonal d * (A * U)) *ᵥ p = Matrix.diagonal d *ᵥ ((A * U) *ᵥ p) from
              (Matrix.mulVec_mulVec _ _ _).symm,
            show (Matrix.diagonal d * (A * U)) *ᵥ q = Matrix.diagonal d *ᵥ ((A * U) *ᵥ q) from
              (Matrix.mulVec_mulVec _ _ _).symm, dot_diag_sel d S hd' hK']
          rfl
        rw [e]
        have := hgood p q
        unfold gramRad
        convert this using 2
      linarith
    have hf1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * U) :=
      (continuous_id.matrix_mul continuous_const).measurable
    have hf2 := BstLean.Part153.measurable_submatrix_rows (p := M) (m := D) σ
    have hmap1 : (gaussMat M k v).map (fun A => A * U) = gaussMat M D v := by
      have h := BstLean.Part182.eb_rot (M := M) (k := k) (K := M) (d := D) hv.le
        (1 : Matrix (Fin M) (Fin M) ℝ) U (by simp) hU
      simpa using h
    have hmap2 := BstLean.Part153.gaussMat_submatrix_rows (p := M) (m := D) v σ σ.injective
    have hT := gaussian_gram_tail hKpos hD hv hυ
    have hμ : (gaussMat M k v) (f ⁻¹' Bad) ≤ (gaussMat K' D v) Bad := by
      calc (gaussMat M k v) (f ⁻¹' Bad)
          = (gaussMat M k v) ((fun A => A * U) ⁻¹'
              ((fun B : Matrix (Fin M) (Fin D) ℝ => B.submatrix σ id) ⁻¹' Bad)) := rfl
        _ ≤ ((gaussMat M k v).map (fun A => A * U))
              ((fun B : Matrix (Fin M) (Fin D) ℝ => B.submatrix σ id) ⁻¹' Bad) :=
            Measure.le_map_apply hf1.aemeasurable _
        _ = (gaussMat M D v) ((fun B : Matrix (Fin M) (Fin D) ℝ => B.submatrix σ id) ⁻¹' Bad) := by
            rw [hmap1]
        _ ≤ ((gaussMat M D v).map (fun B : Matrix (Fin M) (Fin D) ℝ => B.submatrix σ id)) Bad :=
            Measure.le_map_apply hf2.aemeasurable _
        _ = (gaussMat K' D v) Bad := by rw [hmap2]
    haveI : IsProbabilityMeasure (gaussMat K' D v) := by unfold gaussMat; infer_instance
    calc (gaussMat M k v).real {A | v * gramRad (K' : ℝ) D υ < gramDev v d U A}
        ≤ (gaussMat M k v).real (f ⁻¹' Bad) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (gaussMat K' D v).real Bad := ENNReal.toReal_mono (measure_ne_top _ _) hμ
      _ ≤ 2 * exp (-υ ^ 2 / 2) := hT

end BstLean.Part246

namespace BstLean.Part246
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part130 (normSq normSq_nonneg gaussMat)
open BstLean.Part152 (opN opN_nonneg opN_continuous)
open BstLean.Part244 (gramDev gramDev_mulU)

lemma measurable_gramPair {M k D : ℕ} (v υ : ℝ) (U : Matrix (Fin k) (Fin D) ℝ) :
    Measurable (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin k) ℝ =>
      v * gramRad (∑ i, q.1 i) D υ - gramDev v q.1 U q.2) := by
  have hdiag : Continuous (fun f : Fin M → ℝ => Matrix.diagonal f) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · subst h; exact continuous_apply i
    · exact continuous_const
  have hB : Continuous (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin k) ℝ =>
      Matrix.diagonal q.1 * (q.2 * U)) :=
    (hdiag.comp continuous_fst).matrix_mul (continuous_snd.matrix_mul continuous_const)
  have hsum : Continuous (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin k) ℝ => ∑ i, q.1 i) :=
    continuous_finset_sum _ fun i _ => (continuous_apply i).comp continuous_fst
  have hdev : Continuous (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin k) ℝ => gramDev v q.1 U q.2) := by
    unfold gramDev
    exact opN_continuous.comp ((hB.matrix_transpose.matrix_mul hB).sub
      ((continuous_const.mul hsum).smul continuous_const))
  have hrad : Measurable (fun q : (Fin M → ℝ) × Matrix (Fin M) (Fin k) ℝ =>
      v * gramRad (∑ i, q.1 i) D υ) := by
    unfold gramRad
    have hs := hsum.measurable
    fun_prop
  exact hrad.sub hdev.measurable

/-- **Conditional row-selected Gram tail.** If the `{0,1}` selection depends only on `A·P`
(`P` an orthogonal projection) and `P·U = 0` (`U` with orthonormal columns), then the centred
Gram deviation of `diag(d(A P)) · A · U` exceeds `v · gramRad` with probability at most
`2 e^{-υ²/2}`. -/
theorem split_gram_tail {M k D : ℕ} (hD : 1 ≤ D) {v υ : ℝ} (hv : 0 < v) (hυ : 0 ≤ υ)
    (P : Matrix (Fin k) (Fin k) ℝ) (hPs : Pᵀ = P) (hPi : P * P = P)
    (U : Matrix (Fin k) (Fin D) ℝ) (hU : Uᵀ * U = 1) (hPU : P * U = 0)
    (dF : Matrix (Fin M) (Fin k) ℝ → Fin M → ℝ) (hdF : Measurable dF)
    (hd01 : ∀ B i, dF B i = 0 ∨ dF B i = 1) :
    (gaussMat M k v).real {A | v * gramRad (∑ i, dF (A * P) i) D υ <
      gramDev v (dF (A * P)) U A} ≤ 2 * exp (-υ ^ 2 / 2) := by
  classical
  haveI hPμ : IsProbabilityMeasure (gaussMat M k v) := by unfold gaussMat; infer_instance
  have hg1 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * P) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg2 : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hg : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => (A * P, A * (1 - P))) :=
    hg1.prodMk hg2
  set S : Set (Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ) :=
    {q | v * gramRad (∑ i, dF q.1 i) D υ < gramDev v (dF q.1) U q.2} with hSd
  have hSm : MeasurableSet S := by
    have hm := (measurable_gramPair (M := M) (k := k) v υ U).comp
      ((hdF.comp measurable_fst).prodMk measurable_snd)
    have : S = {q | (fun q : Matrix (Fin M) (Fin k) ℝ × Matrix (Fin M) (Fin k) ℝ =>
        v * gramRad (∑ i, dF q.1 i) D υ - gramDev v (dF q.1) U q.2) q < 0} := by
      ext q; simp only [hSd, mem_setOf_eq, sub_neg]
    rw [this]
    exact measurableSet_lt hm measurable_const
  have e : {A : Matrix (Fin M) (Fin k) ℝ | v * gramRad (∑ i, dF (A * P) i) D υ <
      gramDev v (dF (A * P)) U A} = (fun A => (A * P, A * (1 - P))) ⁻¹' S := by
    ext A
    simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, gramDev_mulU v _ P U hPU]
  have hbound : (gaussMat M k v) {A : Matrix (Fin M) (Fin k) ℝ |
      v * gramRad (∑ i, dF (A * P) i) D υ < gramDev v (dF (A * P)) U A} ≤
      ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by
    rw [e, ← Measure.map_apply hg hSm, BstLean.Part182.eb_colsplit v P hPs hPi]
    set μ₁ := (gaussMat M k v).map (fun A => A * P)
    set μ₂ := (gaussMat M k v).map (fun A => A * (1 - P))
    have : IsProbabilityMeasure μ₁ := inferInstance
    have : IsProbabilityMeasure μ₂ := inferInstance
    rw [Measure.prod_apply hSm]
    have hle : ∀ B, μ₂ (Prod.mk B ⁻¹' S) ≤ ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by
      intro B
      have hT : MeasurableSet (Prod.mk B ⁻¹' S) := measurable_prodMk_left hSm
      rw [Measure.map_apply hg2 hT]
      have e2 : (fun A : Matrix (Fin M) (Fin k) ℝ => A * (1 - P)) ⁻¹' (Prod.mk B ⁻¹' S) =
          {A | v * gramRad (∑ i, dF B i) D υ < gramDev v (dF B) U A} := by
        ext A; simp only [hSd, Set.mem_preimage, Set.mem_setOf_eq, gramDev_mulU v _ P U hPU]
      rw [e2]
      have h := rowsel_gram_tail hD hv hυ (dF B) (hd01 B) U hU
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
    calc ∫⁻ B, μ₂ (Prod.mk B ⁻¹' S) ∂μ₁ ≤ ∫⁻ _B, ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) ∂μ₁ :=
          lintegral_mono hle
      _ = ENNReal.ofReal (2 * exp (-υ ^ 2 / 2)) := by rw [lintegral_const, measure_univ, mul_one]
  have h0 : 0 ≤ 2 * exp (-υ ^ 2 / 2) := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal h0 hbound)

end BstLean.Part246

