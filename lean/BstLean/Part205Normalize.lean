import BstLean.Part205ANOVA
import BstLean.Part205Radial

/-! Measurable constant-energy normalization with an explicit zero-vector convention. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part132 BstLean.Part139

section
variable {Ω : Type*} {m : ℕ} (Q : ℝ) (g : Ω → Fin m → ℝ)

noncomputable def radialWeight (x : Ω) : ℝ := nrm (g x) / √Q

noncomputable def normalizeInput (x : Ω) : Fin m → ℝ :=
  if normSq (g x) = 0 then √Q • e0 m else (√Q / nrm (g x)) • g x

lemma normalizeInput_normSq (hm : 1 ≤ m) (hQ : 0 < Q) (x : Ω) :
    normSq (normalizeInput Q g x) = Q := by
  by_cases hg : normSq (g x) = 0
  · simp [normalizeInput, hg, normSq_smul, BstLean.Part130.normSq_e0 hm,
      Real.sq_sqrt hQ.le]
  · rw [normalizeInput, if_neg hg, normSq_smul, div_pow, nrm_sq, Real.sq_sqrt hQ.le]
    exact div_mul_cancel₀ Q hg

lemma radialWeight_nonneg (hQ : 0 < Q) (x : Ω) : 0 ≤ radialWeight Q g x :=
  div_nonneg (nrm_nonneg _) (Real.sqrt_nonneg _)

lemma radialWeight_sq (hQ : 0 < Q) (x : Ω) :
    radialWeight Q g x ^ 2 = normSq (g x) / Q := by
  unfold radialWeight
  rw [div_pow, nrm_sq, Real.sq_sqrt hQ.le]

lemma normalizeInput_factor (hQ : 0 < Q) (x : Ω) :
    g x = radialWeight Q g x • normalizeInput Q g x := by
  have hc : √Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  by_cases hg : normSq (g x) = 0
  · have hz := normSq_eq_zero hg
    simp [normalizeInput, radialWeight, hz, nrm, normSq]
  · have hn : nrm (g x) ≠ 0 := by
      intro hn
      have hs := nrm_sq (g x)
      rw [hn, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
      exact hg hs.symm
    rw [normalizeInput, if_neg hg]
    ext j
    simp only [radialWeight, Pi.smul_apply, smul_eq_mul]
    field_simp

end

section
variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ} (Q : ℝ) (g : Ω → Fin m → ℝ)
variable (hg : ∀ j, BM (fun x => g x j))
include hg

lemma measurable_radialWeight : Measurable (radialWeight Q g) := by
  have hgm : Measurable g := measurable_pi_iff.mpr fun j => (hg j).1
  exact (measurable_normSq.comp hgm).sqrt.div_const _

lemma measurable_normalizeInput : Measurable (normalizeInput Q g) := by
  have hgm : Measurable g := measurable_pi_iff.mpr fun j => (hg j).1
  have hn : Measurable (fun x => nrm (g x)) := (measurable_normSq.comp hgm).sqrt
  exact Measurable.ite (measurableSet_eq_fun (measurable_normSq.comp hgm) measurable_const)
    measurable_const ((measurable_const.div hn).smul hgm)

lemma radialWeight_bm : BM (radialWeight Q g) := by
  have hB : BM (fun x => normSq (g x)) := BM.sum _ fun j _ => (hg j).sq
  obtain ⟨-, B, hBbound⟩ := hB
  refine ⟨measurable_radialWeight Q g hg, √B / √Q, ?_⟩
  intro x
  unfold radialWeight
  rw [abs_div, abs_of_nonneg (nrm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right
    (Real.sqrt_le_sqrt ((le_abs_self _).trans (hBbound x))) (Real.sqrt_nonneg _)

lemma normalizeInput_bm (hm : 1 ≤ m) (hQ : 0 < Q) (j : Fin m) :
    BM (fun x => normalizeInput Q g x j) := by
  refine ⟨(measurable_pi_apply j).comp (measurable_normalizeInput Q g hg), √Q, ?_⟩
  intro x
  have h := Finset.single_le_sum (f := fun j => normalizeInput Q g x j ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ j)
  change normalizeInput Q g x j ^ 2 ≤ normSq (normalizeInput Q g x) at h
  rw [normalizeInput_normSq Q g hm hQ] at h
  exact Real.abs_le_sqrt h

lemma radialWeight_second (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hQ : 0 < Q) (hQeq : ∫ x, normSq (g x) ∂μ = Q) :
    ∫ x, radialWeight Q g x ^ 2 ∂μ = 1 := by
  simp_rw [radialWeight_sq Q g hQ]
  rw [integral_div, hQeq, div_self hQ.ne']

end
end BstLean.Part205

#print axioms BstLean.Part205.normalizeInput_normSq
#print axioms BstLean.Part205.normalizeInput_factor
#print axioms BstLean.Part205.normalizeInput_bm
#print axioms BstLean.Part205.radialWeight_second
