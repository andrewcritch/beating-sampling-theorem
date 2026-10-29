import BstLean.Part215Mixed
import BstLean.Part209Sharp

/-! The projected-kernel average and the shared-weight error average. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part200

/-- The Euclidean norm commutes with averaging as an inequality. -/
theorem nrm_integral_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {n : ℕ} {f : X → Fin n → ℝ}
    (hi : Integrable f μ) (hN : Integrable (fun x => nrm (f x)) μ) :
    nrm (∫ x, f x ∂μ) ≤ ∫ x, nrm (f x) ∂μ := by
  let b := ∫ x, f x ∂μ
  have hdot : Integrable (fun x => ∑ i, f x i * b i) μ :=
    integrable_finset_sum _ fun i _ => (hi.eval i).mul_const _
  have he : (∫ x, ∑ i, f x i * b i ∂μ) = normSq b := by
    rw [integral_finset_sum _ fun i _ => (hi.eval i).mul_const _]
    simp only [integral_mul_const, normSq, sq]
    apply Finset.sum_congr rfl
    intro i _
    have he := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi
    change (∫ x, f x i ∂μ) = b i at he
    change (∫ x, f x i ∂μ) * b i = b i * b i
    rw [he]
  have hb := integral_mono hdot (hN.mul_const (nrm b)) fun x =>
    (le_abs_self _).trans (abs_dot_le_nrm (f x) b)
  rw [he, integral_mul_const, ← nrm_sq] at hb
  have h0 : (0 : ℝ) ≤ ∫ x, nrm (f x) ∂μ := integral_nonneg fun x => nrm_nonneg (f x)
  nlinarith [nrm_nonneg b]

/-- Averaging the second input never increases the weight moment allowance. -/
theorem average_nrm_pow_le {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {n s : ℕ} (hs : 1 ≤ s) {f : X → Fin n → ℝ}
    (hf : Measurable f) (hi : Integrable f μ)
    (hN : Integrable (fun x => nrm (f x)) μ) :
    ENNReal.ofReal (nrm (∫ x, f x ∂μ)) ^ s ≤
      ∫⁻ x, ENNReal.ofReal (nrm (f x)) ^ s ∂μ := by
  have h := lp_mono_nat (μ := μ) ((BstLean.Part130.measurable_normSq.comp hf).sqrt)
    (fun x => nrm_nonneg (f x)) (q := 1) (by norm_num) hs
  simp only [pow_one, Nat.cast_one, div_one, ENNReal.rpow_one] at h
  have hb : ENNReal.ofReal (nrm (∫ x, f x ∂μ)) ≤
      ∫⁻ x, ENNReal.ofReal (nrm (f x)) ∂μ :=
    (ENNReal.ofReal_le_ofReal (nrm_integral_le hi hN)).trans
      (ofReal_integral_le_lintegral (fun x => nrm_nonneg (f x)))
  have h' := pow_le_pow_left' (hb.trans h) s
  rw [BstLean.Part152.enn_root_pow _ hs] at h'
  simpa only [nrm, Function.comp_apply, ENNReal.ofReal_pow (sqrt_nonneg _)] using h'

/-- This is the deterministic projected-kernel average under the chosen input distribution. -/
noncomputable def idealAverage {n : ℕ} (μ : Measure (Fin n → ℝ)) (x : Fin n → ℝ) :
    Fin n → ℝ := ∫ x', pairIdeal x x' ∂μ

/-- This average uses the same matrices at both inputs. -/
noncomputable def errorAverage {n : ℕ} (μ : Measure (Fin n → ℝ))
    (a : Matrix (Fin (n ^ 2)) (Fin n) ℝ × Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  ∫ x', (n : ℝ)⁻¹ • pairVector a.1 a.2 x x' - pairIdeal x x' ∂μ

#print axioms nrm_integral_le
#print axioms average_nrm_pow_le
end BstLean.Part215
