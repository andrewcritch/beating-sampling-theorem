import BstLean.Part216Energy
import BstLean.Part216Clock

/-! The BE order18 moment, including zero scale and zero row count. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part202

variable {V P : Type*} [MeasurableSpace V] [MeasurableSpace P]
variable {μ : Measure V} [IsProbabilityMeasure μ]
variable {ν : Measure P} [IsProbabilityMeasure ν] {d m : ℕ}
variable {a : V → Fin d → ℝ} {ell : ℝ}

lemma whole_sum_zero_scale (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N : ℕ) (hs : rowScale μ a ell = 0) :
    wholeRowSum S N =ᵐ[Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))] 0 := by
  have hv := row_factorial_all S ha hK 2 (by norm_num)
  rw [hs] at hv
  have he : ∫ q, |rowFluct S q| ^ 2 ∂ν.prod (stdGauss (Fin m)) = 0 :=
    le_antisymm (by simpa using hv) (integral_nonneg fun q => sq_nonneg _)
  have hrow := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg (|rowFluct S q|))
    (row_square_integrable S ha hK)).mp he
  have hz : ∀ᵐ q ∂ν.prod (stdGauss (Fin m)), rowFluct S q = 0 := by
    filter_upwards [hrow] with q hq
    exact abs_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hq)
  have heval : ∀ j : Fin N, ∀ᵐ q ∂Measure.pi (fun _ : Fin N => ν.prod (stdGauss (Fin m))),
      rowFluct S (q j) = 0 := fun j =>
    (measurePreserving_eval (fun _ : Fin N => ν.prod (stdGauss (Fin m))) j).quasiMeasurePreserving.ae hz
  filter_upwards [ae_all_iff.mpr heval] with q hq
  simp [wholeRowSum, hq]

/-- The paper BE moment follows from the analytic tail on the whole-row product.
The coefficient keeps the Gaussian order9 and exponential order18 factorials separate. -/
theorem whole_sum_order18 (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (N : ℕ) :
    ∫⁻ q, ENNReal.ofReal (|wholeRowSum S N q| ^ 18)
      ∂(Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))) ≤
      ENNReal.ofReal ((sqrt (2 * (2 * N * rowScale μ a ell ^ 2)) *
          (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
        (BstLean.Part202.beta * rowScale μ a ell) * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)) ^ 18) := by
  by_cases hscale : rowScale μ a ell = 0
  · have hz : (fun q => ENNReal.ofReal (|wholeRowSum S N q| ^ 18)) =ᵐ[
        Measure.pi fun _ : Fin N => ν.prod (stdGauss (Fin m))] fun _ => 0 :=
      (whole_sum_zero_scale S ha hK N hscale).mono fun q hq => by
        simp only [hq, Pi.zero_apply, abs_zero, zero_pow (by norm_num : (18 : ℕ) ≠ 0), ENNReal.ofReal_zero]
    rw [lintegral_congr_ae hz, lintegral_zero]
    exact zero_le
  by_cases hN : N = 0
  · subst N
    simp [wholeRowSum]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hspos : 0 < rowScale μ a ell := lt_of_le_of_ne rowScale_nonneg (Ne.symm hscale)
  have hY : Measurable (wholeRowSum S N) := Finset.measurable_sum _
    (fun j _ => S.measurable_fluct.comp (measurable_pi_apply j))
  apply sqrt_linear_tail_order18 hY (sqrt_nonneg _) (mul_pos beta_pos hspos)
  intro τ hτ
  have h := whole_sum_tail S ha hK N hNpos hspos hτ
  rw [sqrt_mul (by positivity : 0 ≤ 2 * (2 * (N : ℝ) * rowScale μ a ell ^ 2))] at h
  exact h

/-- For `N=n²`, the Gaussian coefficient is `2 n scale`, with the actual width. -/
theorem whole_sum_order18_width (S : RowSplit μ ν a m ell) (ha : Measurable a)
    {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) (n : ℕ) :
    ∫⁻ q, ENNReal.ofReal (|wholeRowSum S (n ^ 2) q| ^ 18)
      ∂(Measure.pi fun _ : Fin (n ^ 2) => ν.prod (stdGauss (Fin m))) ≤
      ENNReal.ofReal ((rowScale μ a ell *
        (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
          BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹))) ^ 18) := by
  have h := whole_sum_order18 S ha hK (n ^ 2)
  have hs0 : 0 ≤ rowScale μ a ell := rowScale_nonneg
  have he : sqrt (2 * (2 * ((n ^ 2 : ℕ) : ℝ) * rowScale μ a ell ^ 2)) =
      2 * n * rowScale μ a ell := by
    rw [show 2 * (2 * ((n ^ 2 : ℕ) : ℝ) * rowScale μ a ell ^ 2) =
      (2 * n * rowScale μ a ell) ^ 2 by push_cast; ring,
      sqrt_sq (by positivity)]
  have hex : 2 * n * rowScale μ a ell * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
      (BstLean.Part202.beta * rowScale μ a ell) * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) =
      rowScale μ a ell * (2 * n * (2 * ((9 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹) +
        BstLean.Part202.beta * (2 * ((18 : ℕ).factorial : ℝ)) ^ ((18 : ℝ)⁻¹)) := by ring
  rw [he, hex] at h
  exact h

#print axioms whole_sum_zero_scale
#print axioms whole_sum_order18
#print axioms whole_sum_order18_width
end BstLean.Part216
