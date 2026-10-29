import BstLean.Part199Events

/-! Part 235: one Markov payment for a measurable fixed-pair failure set. -/
namespace BstLean.Part235
open MeasureTheory
open scoped ENNReal

/-- Integrate the actual pair failure before applying Markov. The pair set can use
a deterministic core/wide class and a deterministic overlap cell. -/
theorem pair_mass_charge {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
    (ν : Measure A) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (S : Set (A × X)) (hS : MeasurableSet S) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hpair : ∀ x, ν.real ((fun a => (a, x)) ⁻¹' S) ≤ δ) :
    ν.real {a | δ / ε < μ.real (Prod.mk a ⁻¹' S)} ≤ ε := by
  have hT : ∫⁻ a, μ (Prod.mk a ⁻¹' S) ∂ν ≤ ENNReal.ofReal δ := by
    rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
    calc
      ∫⁻ x, ν ((fun a => (a, x)) ⁻¹' S) ∂μ
          ≤ ∫⁻ _x, ENNReal.ofReal δ ∂μ := by
        apply lintegral_mono
        intro x
        change ν ((fun a => (a, x)) ⁻¹' S) ≤ ENNReal.ofReal δ
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (hpair x)
      _ = ENNReal.ofReal δ := by rw [lintegral_const, measure_univ, mul_one]
  have hset : {a | δ / ε < μ.real (Prod.mk a ⁻¹' S)} =
      {a | ENNReal.ofReal (δ / ε) < μ (Prod.mk a ⁻¹' S)} := by
    ext a
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact (ENNReal.ofReal_lt_ofReal_iff
        (lt_of_le_of_lt (div_nonneg hδ hε.le) h)).2 h
    · intro h
      have ht := ENNReal.toReal_strict_mono (measure_ne_top μ _) h
      rwa [ENNReal.toReal_ofReal (div_nonneg hδ hε.le)] at ht
  rw [hset]
  have hm : Measurable (fun a => μ (Prod.mk a ⁻¹' S)) :=
    measurable_measure_prodMk_left hS
  by_cases hz : δ = 0
  · subst δ
    have hi : ∫⁻ a, μ (Prod.mk a ⁻¹' S) ∂ν = 0 := by simpa using hT
    have hae := (lintegral_eq_zero_iff hm).1 hi
    have he : ν {a | ENNReal.ofReal (0 / ε) < μ (Prod.mk a ⁻¹' S)} = 0 := by
      refine measure_mono_null (fun a ha => ?_) (ae_iff.1 hae)
      simp only [Set.mem_ofPred_eq, zero_div, ENNReal.ofReal_zero] at ha ⊢
      exact ne_of_gt ha
    rw [Measure.real, he, ENNReal.toReal_zero]
    exact hε.le
  have hd : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
  have hk := mul_meas_ge_le_lintegral₀ (μ := ν) hm.aemeasurable
    (ENNReal.ofReal (δ / ε))
  have hs : {a | ENNReal.ofReal (δ / ε) < μ (Prod.mk a ⁻¹' S)} ⊆
      {a | ENNReal.ofReal (δ / ε) ≤ μ (Prod.mk a ⁻¹' S)} :=
    fun a h => le_of_lt (show ENNReal.ofReal (δ / ε) < μ (Prod.mk a ⁻¹' S) from h)
  have hb : ENNReal.ofReal (δ / ε) *
      ν {a | ENNReal.ofReal (δ / ε) < μ (Prod.mk a ⁻¹' S)} ≤ ENNReal.ofReal δ :=
    (mul_le_mul' le_rfl (measure_mono hs)).trans (hk.trans hT)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg hδ hε.le),
    ENNReal.toReal_ofReal hδ] at hr
  rw [Measure.real]
  have hq : 0 < δ / ε := div_pos hd hε
  have hu : (ν {a | ENNReal.ofReal (δ / ε) < μ (Prod.mk a ⁻¹' S)}).toReal ≤
      δ / (δ / ε) := by
    rw [le_div_iff₀ hq]
    simpa only [mul_comm] using hr
  rwa [div_div_cancel₀ hd.ne'] at hu

end BstLean.Part235
