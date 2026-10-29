import BstLean.Part242WeightedVariance
import BstLean.Part242MixtureConstants

/-! Conditional variance identities supply the improved integrated moments. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part162 (nrm)

variable {V : Type*} [MeasurableSpace V]

lemma good_mean_sq_lower (ν : Measure V) [IsProbabilityMeasure ν]
    {G : Set V} (hG : MeasurableSet G) (hm : 0 < ν.real G)
    {z : V → ℝ} (mz : Measurable z) {M σ : ℝ} (hM : ∀ v, |z v| ≤ M)
    (hσ : 0 ≤ σ) (hcut : ∀ v ∈ G, σ ≤ z v) : σ ^ 2 ≤ goodMeanSq ν G z := by
  haveI := BstLean.Part162.nrm_prob ν hG hm
  have iz := BstLean.Part162.intB (μ := nrm ν G) mz hM
  have h := integral_mono_ae (integrable_const σ) iz
    ((BstLean.Part162.nrm_ae_mem ν hG).mono fun v hv => hcut v hv)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact pow_le_pow_left₀ hσ h 2

lemma good_mean_sq_pos (ν : Measure V) [IsProbabilityMeasure ν]
    {G : Set V} (hG : MeasurableSet G) (hm : 0 < ν.real G)
    {z : V → ℝ} (mz : Measurable z) {M σ : ℝ} (hM : ∀ v, |z v| ≤ M)
    (hσ : 0 < σ) (hcut : ∀ v ∈ G, σ ≤ z v) : 0 < goodMeanSq ν G z := by
  haveI := BstLean.Part162.nrm_prob ν hG hm
  have iz := BstLean.Part162.intB (μ := nrm ν G) mz hM
  have h := integral_mono_ae (integrable_const σ) iz
    ((BstLean.Part162.nrm_ae_mem ν hG).mono fun v hv => hcut v hv)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  unfold goodMeanSq
  have hp : 0 < ∫ v, z v ∂nrm ν G := hσ.trans_le h
  positivity

lemma normalized_location_eq (ν : Measure V) {G : Set V} {f : V → ℝ}
    {C S0 : ℝ} (hC : 0 ≤ C) (hS0 : 0 < S0) :
    (∫ v, (sqrt (C / S0) * (f v - ∫ u, f u ∂nrm ν G)) ^ 2 ∂nrm ν G) =
      C / S0 * conditionalVariance (nrm ν G) f := by
  simp_rw [mul_pow, sq_sqrt (div_nonneg hC hS0.le)]
  rw [integral_const_mul]
  rfl

variable {A : Type*} [MeasurableSpace A]

/-- The location input can use an upper centre bound.
The energy input is the exact normalized conditional second error moment. -/
theorem integrated_moments_SY2 (ρ : Measure A) (ν : Measure V) [SFinite ρ]
    [IsProbabilityMeasure ν] (hmass : ρ univ ≤ 1)
    {K : Set A} (hK : MeasurableSet K) {G : Set (A × V)} (hG : MeasurableSet G)
    (n : ℕ) {dw dl Γ Vbound η χ : ℝ}
    (hdw : 0 ≤ dw) (hdl : 0 < dl) (hη1 : η < 1) (hχ : 0 ≤ χ)
    {z f : A × V → ℝ} (mz : Measurable z) (mf : Measurable f)
    {Mz Mf : ℝ} (hzB : ∀ a v, |z (a, v)| ≤ Mz) (hfB : ∀ a v, |f (a, v)| ≤ Mf)
    (hgood : ∀ a ∈ K, 1 - η ≤ ν.real {v | (a, v) ∈ G})
    (hcut : ∀ a ∈ K, ∀ v, (a, v) ∈ G →
      |z (a, v) - latitudeMean ν z a| ≤ dw ∧ sqrt dl ≤ z (a, v))
    (hzvar : LBound (ρ.restrict K) 12
      (fun a => conditionalVariance ν (fun v => z (a, v))) Vbound)
    (hfvar : LBound (ρ.restrict K) 12
      (fun a => conditionalVariance ν (fun v => f (a, v))) Vbound)
    (hR : LBound (ρ.restrict K) 4
      (fun a => 1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))) Γ)
    {E D : A → ℝ} (mE : Measurable E) (mD : Measurable D)
    (hE : ∀ a ∈ K, E a =
      ∫ v, (z (a, v) ^ 2 / (∫ u, z (a, u) ^ 2 ∂nrm ν {v | (a, v) ∈ G}) - 1) ^ 2
        ∂nrm ν {v | (a, v) ∈ G})
    (hD : ∀ a ∈ K, 0 ≤ D a ∧ D a ≤
      (n : ℝ) * χ / (∫ u, z (a, u) ^ 2 ∂nrm ν {v | (a, v) ∈ G}) *
        conditionalVariance (nrm ν {v | (a, v) ∈ G}) (fun v => f (a, v))) :
    LBound (ρ.restrict K) 2 E (mixA dw dl Γ Vbound η) ∧
    LBound (ρ.restrict K) 3 E (mixA dw dl Γ Vbound η) ∧
    LBound (ρ.restrict K) 2 D (mixD n χ Γ Vbound η) ∧
    LBound (ρ.restrict K) 3 D (mixD n χ Γ Vbound η) := by
  have hmK : (ρ.restrict K) univ ≤ 1 := (Measure.restrict_le_self univ).trans hmass
  have hz4 := hzvar.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 12) hmK
  have hf4 := hfvar.lower (by norm_num) (by norm_num) (by norm_num : (4 : ℝ≥0∞) ≤ 12) hmK
  obtain ⟨hE2, hE3⟩ := SY2_variance_constants (dw := dw) (d := dl) hη1 hz4 hzvar hR
  obtain ⟨hD2, hD3⟩ := SY2_location_constants n hχ hη1 hf4 hfvar hR
  have ptE : ∀ a ∈ K, |E a| ≤
      |(4 * (1 + dw / sqrt dl) ^ 2 / (1 - η)) *
        (conditionalVariance ν (fun v => z (a, v)) *
          (1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))))| := by
    intro a ha
    have ms : MeasurableSet {v | (a, v) ∈ G} := hG.preimage measurable_prodMk_left
    have hm : 0 < ν.real {v | (a, v) ∈ G} := by have := hgood a ha; linarith
    have mzA : Measurable (fun v => z (a, v)) := mz.comp measurable_prodMk_left
    have hh := weighted_eps_variance ms hm mzA (hzB a)
      hdw (sqrt_pos.mpr hdl) (hgood a ha) hη1 (hcut a ha)
    rw [hE a ha, abs_of_nonneg (integral_nonneg fun v => sq_nonneg _)]
    have hv0 : 0 ≤ conditionalVariance ν (fun v => z (a, v)) := integral_nonneg fun v => sq_nonneg _
    rw [abs_of_nonneg (by unfold goodMeanSq; positivity)]
    exact hh.trans_eq (by ring)
  have ptD : ∀ a ∈ K, |D a| ≤
      |((n : ℝ) * χ / (1 - η)) *
        (conditionalVariance ν (fun v => f (a, v)) *
          (1 / goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v))))| := by
    intro a ha
    have ms : MeasurableSet {v | (a, v) ∈ G} := hG.preimage measurable_prodMk_left
    have hm : 0 < ν.real {v | (a, v) ∈ G} := by have := hgood a ha; linarith
    have mzA : Measurable (fun v => z (a, v)) := mz.comp measurable_prodMk_left
    have mgm := good_mean_sq_pos ν ms hm mzA (hzB a) (sqrt_pos.mpr hdl)
      (fun v hv => (hcut a ha v hv).2)
    haveI := BstLean.Part162.nrm_prob ν ms hm
    have hS0 : goodMeanSq ν {v | (a, v) ∈ G} (fun v => z (a, v)) ≤
        ∫ v, z (a, v) ^ 2 ∂nrm ν {v | (a, v) ∈ G} := BstLean.Part162.mean_sq_le mzA (hzB a)
    have hS0p := mgm.trans_le hS0
    have hnχ : 0 ≤ (n : ℝ) * χ := by positivity
    have mfA : Measurable (fun v => f (a, v)) := mf.comp measurable_prodMk_left
    have hh := weighted_location_variance ms hm mfA (hfB a)
      mgm hS0 hnχ (hgood a ha) hη1
    rw [normalized_location_eq ν hnχ hS0p] at hh
    rw [abs_of_nonneg (hD a ha).1]
    have hv0 : 0 ≤ conditionalVariance ν (fun v => f (a, v)) := integral_nonneg fun v => sq_nonneg _
    rw [abs_of_nonneg (by unfold goodMeanSq; positivity)]
    exact (hD a ha).2.trans (hh.trans_eq (by ring))
  have aeE := (ae_restrict_iff' (μ := ρ) hK).mpr (Filter.Eventually.of_forall ptE)
  have aeD := (ae_restrict_iff' (μ := ρ) hK).mpr (Filter.Eventually.of_forall ptD)
  exact ⟨hE2.mono mE aeE, hE3.mono mE aeE, hD2.mono mD aeD, hD3.mono mD aeD⟩

end BstLean.Part242
