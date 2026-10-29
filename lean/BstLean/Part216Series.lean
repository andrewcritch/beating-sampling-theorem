import BstLean.Part202Bernstein
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! Absolute convergence of the Bernstein exponential remainder. -/
namespace BstLean.Part216
open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal

lemma exp_remainder_series (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 2) / ((k + 2).factorial : ℝ)) (exp x - 1 - x) := by
  have h : HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (exp x) := by
    simpa only [smul_eq_mul, ← div_eq_inv_mul, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x)
  have ht := (hasSum_nat_add_iff' 2).mpr h
  simpa [Finset.sum_range_succ, sub_sub] using ht

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Factorial absolute moments justify the exponential remainder on `b*s < 1`. -/
theorem factorial_remainder {Y : Ω → ℝ} (hY : Measurable Y)
    (hi : ∀ k : ℕ, Integrable (fun x => |Y x| ^ k) μ)
    {v b s : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hs : 0 ≤ s) (hbs : b * s < 1)
    (hM : ∀ k : ℕ, 2 ≤ k → ∫ x, |Y x| ^ k ∂μ ≤
      (k.factorial : ℝ) / 2 * v * b ^ (k - 2)) :
    Integrable (fun x => exp (s * |Y x|)) μ ∧
    ∫ x, (exp (s * |Y x|) - 1 - s * |Y x|) ∂μ ≤
      v * s ^ 2 / (2 * (1 - b * s)) := by
  let F : ℕ → Ω → ℝ := fun k x => (s * |Y x|) ^ (k + 2) / ((k + 2).factorial : ℝ)
  let C : ℕ → ℝ := fun k => v * s ^ 2 / 2 * (b * s) ^ k
  have hF0 : ∀ k x, 0 ≤ F k x := fun k x => by dsimp [F]; positivity
  have hFi : ∀ k, Integrable (F k) μ := fun k => by
    simp only [F, mul_pow]
    exact ((hi (k + 2)).const_mul _).div_const _
  have hFB : ∀ k, ∫ x, F k x ∂μ ≤ C k := by
    intro k
    simp only [F, mul_pow, integral_div, integral_const_mul]
    have hm := mul_le_mul_of_nonneg_left (hM (k + 2) (by omega))
      (pow_nonneg hs (k + 2))
    have hf : (0 : ℝ) < (k + 2).factorial := by positivity
    apply (div_le_iff₀ hf).mpr
    dsimp [C]
    simp only [Nat.add_sub_cancel] at hm
    convert hm using 1 <;> ring
  have hCs : Summable C :=
    (summable_geometric_of_lt_one (mul_nonneg hb hs) hbs).mul_left _
  have hIs : Summable (fun k => ∫ x, F k x ∂μ) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg (hF0 k)) hFB hCs
  have hR : ∀ x, (∑' k, F k x) = exp (s * |Y x|) - 1 - s * |Y x| :=
    fun x => (exp_remainder_series _).tsum_eq
  have hRi : Integrable (fun x => exp (s * |Y x|) - 1 - s * |Y x|) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((hY.abs.const_mul s).exp.sub measurable_const |>.sub (hY.abs.const_mul s)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        change 0 ≤ exp (s * |Y x|) - 1 - s * |Y x|
        linarith [Real.add_one_le_exp (s * |Y x|)])).mp
    change (∫⁻ x, ENNReal.ofReal (exp (s * |Y x|) - 1 - s * |Y x|) ∂μ) ≠ ∞
    have he : (fun x => ENNReal.ofReal (exp (s * |Y x|) - 1 - s * |Y x|)) =
        fun x => ∑' k, ENNReal.ofReal (F k x) := by
      funext x
      rw [← hR x, ENNReal.ofReal_tsum_of_nonneg (fun k => hF0 k x)
        (exp_remainder_series _).summable]
    rw [he, lintegral_tsum (fun k => (hY.abs.const_mul s).pow_const (k + 2) |>.div_const _ |>.ennreal_ofReal.aemeasurable)]
    change (∑' k, ∫⁻ x, ENNReal.ofReal (F k x) ∂μ) ≠ ∞
    have heI : ∀ k, ∫⁻ x, ENNReal.ofReal (F k x) ∂μ = ENNReal.ofReal (∫ x, F k x ∂μ) :=
      fun k => (ofReal_integral_eq_lintegral_ofReal (hFi k) (Eventually.of_forall (hF0 k))).symm
    simp_rw [heI]
    exact hIs.tsum_ofReal_ne_top
  refine ⟨?_, ?_⟩
  · have hh := (hRi.add (integrable_const (1 : ℝ))).add ((hi 1).const_mul s)
    simp only [pow_one] at hh
    exact hh.congr (Eventually.of_forall fun x => by
      change (exp (s * |Y x|) - 1 - s * |Y x|) + 1 + s * |Y x| = exp (s * |Y x|)
      ring)
  · have he := integral_tsum_of_summable_integral_norm hFi (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _ _)] using hIs)
    simp_rw [hR] at he
    rw [← he]
    calc ∑' k, ∫ x, F k x ∂μ ≤ ∑' k, C k := hIs.tsum_le_tsum hFB hCs
      _ = _ := by
        dsimp [C]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hb hs) hbs]
        field_simp
        <;> ring

#print axioms factorial_remainder
end BstLean.Part216
