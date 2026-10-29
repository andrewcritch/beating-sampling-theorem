import BstLean.Part56MC_Moments
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! An annihilator criterion for polynomial density under measures with exponential moments. -/

namespace BstLean.Part56

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false in
theorem mc56_annihilator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure E} [IsFiniteMeasure μ] (F : E → ℝ) (hF : MemLp F 2 μ)
    (he : ∀ (L : E →L[ℝ] ℝ) (t : ℝ), MemLp (fun x => Real.exp (t * L x)) 2 μ)
    (hp : ∀ (L : E →L[ℝ] ℝ) (k : ℕ), MemLp (fun x => L x ^ k) 2 μ)
    (hm : ∀ (L : E →L[ℝ] ℝ) (k : ℕ), (∫ x, F x * L x ^ k ∂μ) = 0) :
    F =ᵐ[μ] 0 := by
  let P : E → ℝ := fun x => (‖F x‖ + F x) / 2
  let N : E → ℝ := fun x => (‖F x‖ - F x) / 2
  have hP : MemLp P 2 μ := by
    simpa [P, div_eq_mul_inv, mul_comm] using (hF.norm.add hF).const_mul (1 / 2 : ℝ)
  have hN : MemLp N 2 μ := by
    simpa [N, div_eq_mul_inv, mul_comm] using (hF.norm.sub hF).const_mul (1 / 2 : ℝ)
  have hP0 (x : E) : 0 ≤ P x := by
    dsimp [P]
    exact div_nonneg (by linarith [neg_abs_le (F x)]) (by norm_num)
  have hN0 (x : E) : 0 ≤ N x := by
    dsimp [N]
    exact div_nonneg (by linarith [le_abs_self (F x)]) (by norm_num)
  let μP := μ.withDensity (fun x => ENNReal.ofReal (P x))
  let μN := μ.withDensity (fun x => ENNReal.ofReal (N x))
  have hPf : (∫⁻ x, ENNReal.ofReal (P x) ∂μ) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hP0)).mp
      (hP.integrable (by simp)).hasFiniteIntegral).ne
  have hNf : (∫⁻ x, ENNReal.ofReal (N x) ∂μ) ≠ ∞ :=
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hN0)).mp
      (hN.integrable (by simp)).hasFiniteIntegral).ne
  let : IsFiniteMeasure μP := isFiniteMeasure_withDensity hPf
  let : IsFiniteMeasure μN := isFiniteMeasure_withDensity hNf
  have hPmeas : AEMeasurable (fun x => ENNReal.ofReal (P x)) μ :=
    hP.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hNmeas : AEMeasurable (fun x => ENNReal.ofReal (N x)) μ :=
    hN.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hiP (G : E → ℝ) (hG : MemLp G 2 μ) : Integrable G μP := by
    apply (integrable_withDensity_iff_integrable_smul₀' hPmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp only [ENNReal.toReal_ofReal (hP0 _), smul_eq_mul]
    convert hP.integrable_mul hG using 1
  have hiN (G : E → ℝ) (hG : MemLp G 2 μ) : Integrable G μN := by
    apply (integrable_withDensity_iff_integrable_smul₀' hNmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp only [ENNReal.toReal_ofReal (hN0 _), smul_eq_mul]
    convert hN.integrable_mul hG using 1
  have intP (G : E → ℝ) : (∫ x, G x ∂μP) = ∫ x, P x * G x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hPmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hP0 _), smul_eq_mul]
  have intN (G : E → ℝ) : (∫ x, G x ∂μN) = ∫ x, N x * G x ∂μ := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ hNmeas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hN0 _), smul_eq_mul]
  have hmeas : μP = μN := by
    apply mc56_measure_eq_of_linear_moments
    · intro L t; exact hiP _ (he L t)
    · intro L t; exact hiN _ (he L t)
    · intro L k
      have hip : Integrable (fun x => P x * L x ^ k) μ := by
        convert hP.integrable_mul (hp L k) using 1
      have hin : Integrable (fun x => N x * L x ^ k) μ := by
        convert hN.integrable_mul (hp L k) using 1
      rw [intP, intN, ← sub_eq_zero, ← integral_sub hip hin]
      convert hm L k using 2
      funext x
      dsimp [P, N]
      ring
  have hPN := (withDensity_eq_iff hPmeas hNmeas hPf).mp hmeas
  filter_upwards [hPN] with x hx
  have hx' : P x = N x := (ENNReal.ofReal_eq_ofReal_iff (hP0 x) (hN0 x)).mp hx
  change F x = 0
  dsimp [P, N] at hx'
  linarith

end BstLean.Part56
