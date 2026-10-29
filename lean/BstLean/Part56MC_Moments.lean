import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness

/-! Moment determinacy for finite measures with exponential moments of every order. -/

namespace BstLean.Part56

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem mc56_measure_eq_of_moments {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) ν)
    (hm : ∀ k : ℕ, (∫ x : ℝ, x ^ k ∂μ) = ∫ x : ℝ, x ^ k ∂ν) : μ = ν := by
  have hsμ : integrableExpSet id μ = univ := by
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    exact hμ t
  have hsν : integrableExpSet id ν = univ := by
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    exact hν t
  have haμ : AnalyticOnNhd ℝ (mgf id μ) univ := by
    simpa [hsμ] using (analyticOnNhd_mgf (X := id) (μ := μ))
  have haν : AnalyticOnNhd ℝ (mgf id ν) univ := by
    simpa [hsν] using (analyticOnNhd_mgf (X := id) (μ := ν))
  have he : mgf id μ = mgf id ν := by
    have hf : AnalyticAt ℝ (fun t => mgf id μ t - mgf id ν t) 0 :=
      (haμ 0 (mem_univ 0)).sub (haν 0 (mem_univ 0))
    have hd : ∀ k : ℕ, iteratedDeriv k (fun t => mgf id μ t - mgf id ν t) 0 = 0 := by
      intro k
      rw [iteratedDeriv_fun_sub (haμ 0 (mem_univ 0)).contDiffAt
        (haν 0 (mem_univ 0)).contDiffAt]
      rw [iteratedDeriv_mgf_zero (by simp [hsμ]),
        iteratedDeriv_mgf_zero (by simp [hsν])]
      simpa using sub_eq_zero.mpr (hm k)
    have ho : analyticOrderAt (fun t => mgf id μ t - mgf id ν t) 0 = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro k
      exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr (fun i _ => hd i)
    have hnear : mgf id μ =ᶠ[𝓝 (0 : ℝ)] mgf id ν := by
      filter_upwards [analyticOrderAt_eq_top.mp ho] with t ht
      exact sub_eq_zero.mp ht
    exact haμ.eq_of_eventuallyEq haν hnear
  have hzero : μ = 0 ↔ ν = 0 := by
    have hm0 := hm 0
    simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at hm0
    constructor <;> intro hz
    · subst μ
      have : ν.real univ = 0 := by simpa using hm0.symm
      exact Measure.measure_univ_eq_zero.mp ((ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right
        (measure_ne_top ν univ))
    · subst ν
      have : μ.real univ = 0 := by simpa using hm0
      exact Measure.measure_univ_eq_zero.mp ((ENNReal.toReal_eq_zero_iff _).mp this |>.resolve_right
        (measure_ne_top μ univ))
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  exact eqOn_complexMGF_of_mgf' he hzero (by simp [hsμ])

theorem mc56_measure_eq_of_linear_moments {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), Integrable (fun x => Real.exp (t * L x)) μ)
    (hν : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), Integrable (fun x => Real.exp (t * L x)) ν)
    (hm : ∀ (L : E →L[ℝ] ℝ) (k : ℕ), (∫ x, L x ^ k ∂μ) = ∫ x, L x ^ k ∂ν) :
    μ = ν := by
  have hmap (L : E →L[ℝ] ℝ) : μ.map L = ν.map L := by
    apply mc56_measure_eq_of_moments
    · intro t
      exact (integrable_map_measure (by fun_prop) L.measurable.aemeasurable).mpr (hμ L t)
    · intro t
      exact (integrable_map_measure (by fun_prop) L.measurable.aemeasurable).mpr (hν L t)
    · intro k
      rw [integral_map L.measurable.aemeasurable (by fun_prop),
        integral_map L.measurable.aemeasurable (by fun_prop)]
      exact hm L k
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  rw [← integral_map L.measurable.aemeasurable
    (show AEStronglyMeasurable (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (μ.map L) from (by fun_prop)), hmap L]
  exact integral_map L.measurable.aemeasurable (by fun_prop)

end BstLean.Part56
