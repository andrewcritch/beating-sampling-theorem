import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Cauchy–Schwarz on the independent pair of sphere inputs. -/
namespace BstLean.Part56

open MeasureTheory
open scoped ENNReal

/-- The product integral in the covariance estimate needs the first moment of `S`,
not the second moment of `S`. -/
theorem rkg56_product_cauchy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (R : X × X → ℝ)
    (hR : MemLp R 2 (μ.prod μ)) (S : X → ℝ) (hSm : Measurable S)
    (hS : Integrable S μ) (hS0 : ∀ x, 0 ≤ S x) :
    (∫ p, |R p| * Real.sqrt (S p.1) * Real.sqrt (S p.2) ∂μ.prod μ) ≤
      Real.sqrt (∫ p, R p ^ 2 ∂μ.prod μ) * ∫ x, S x ∂μ := by
  let G : X × X → ℝ := fun p => Real.sqrt (S p.1) * Real.sqrt (S p.2)
  have hG0 (p) : 0 ≤ G p := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hGm : Measurable G :=
    (Real.continuous_sqrt.measurable.comp (hSm.comp measurable_fst)).mul
      (Real.continuous_sqrt.measurable.comp (hSm.comp measurable_snd))
  have hGsq (p) : G p ^ 2 = S p.1 * S p.2 := by
    dsimp [G]
    rw [mul_pow, Real.sq_sqrt (hS0 _), Real.sq_sqrt (hS0 _)]
  have hG : MemLp G 2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2
    simpa only [hGsq] using hS.mul_prod hS
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hR) (by simpa using hG)
  have hnormG0 (p) : ‖G p‖ = G p := Real.norm_of_nonneg (hG0 p)
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, hGsq, hnormG0,
    ← Real.sqrt_eq_rpow, integral_prod_mul, ← pow_two] at hc
  rw [Real.sqrt_sq (integral_nonneg hS0)] at hc
  simpa only [G, mul_assoc] using hc

/-- Integrate a pointwise maximal-correlation bound. -/
theorem rkg56_covariance_cauchy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (R A : X × X → ℝ)
    (hR : MemLp R 2 (μ.prod μ)) (hA : Integrable A (μ.prod μ))
    (S : X → ℝ) (hSm : Measurable S) (hS : Integrable S μ)
    (hS0 : ∀ x, 0 ≤ S x)
    (hbound : ∀ p, A p ≤ |R p| * Real.sqrt (S p.1) * Real.sqrt (S p.2)) :
    (∫ p, A p ∂μ.prod μ) ≤
      Real.sqrt (∫ p, R p ^ 2 ∂μ.prod μ) * ∫ x, S x ∂μ := by
  have hGm : Measurable (fun p : X × X => Real.sqrt (S p.1) * Real.sqrt (S p.2)) :=
    (Real.continuous_sqrt.measurable.comp (hSm.comp measurable_fst)).mul
      (Real.continuous_sqrt.measurable.comp (hSm.comp measurable_snd))
  have hG : MemLp (fun p : X × X => Real.sqrt (S p.1) * Real.sqrt (S p.2))
      2 (μ.prod μ) := by
    apply (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2
    have hs (p : X × X) : (Real.sqrt (S p.1) * Real.sqrt (S p.2)) ^ 2 =
        S p.1 * S p.2 := by
      rw [mul_pow, Real.sq_sqrt (hS0 _), Real.sq_sqrt (hS0 _)]
    simpa only [hs] using hS.mul_prod hS
  have hi : Integrable (fun p => |R p| * Real.sqrt (S p.1) * Real.sqrt (S p.2))
      (μ.prod μ) := by
    have h : MemLp (fun p => ‖R p‖ * (Real.sqrt (S p.1) * Real.sqrt (S p.2)))
        1 (μ.prod μ) := hR.norm.mul hG
    simpa only [Real.norm_eq_abs, mul_assoc] using (memLp_one_iff_integrable.mp h)
  exact (integral_mono hA hi hbound).trans
    (rkg56_product_cauchy μ R hR S hSm hS hS0)

end BstLean.Part56
