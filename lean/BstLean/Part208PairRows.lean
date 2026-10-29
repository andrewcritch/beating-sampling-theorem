import BstLean.Part208Tangential

/-! Part 208: weighted row bounds supply the integrated four-mode gain. -/
namespace BstLean.Part208
open MeasureTheory Real

/-- On a symmetric pair set, both mode factors use its same restriction. -/
theorem indicator_mul_swap {X : Type*} (H : Set (X × X))
    (hHs : ∀ p ∈ H, p.swap ∈ H) (a b : X × X → ℝ) (p : X × X) :
    H.indicator a p * H.indicator b p.swap =
      H.indicator (fun p => a p * b p.swap) p := by
  by_cases hp : p ∈ H
  · simp only [Set.indicator_of_mem hp, Set.indicator_of_mem (hHs p hp)]
  · simp only [Set.indicator_of_notMem hp, zero_mul]

/-- Integrate the row square bounds before applying Cauchy--Schwarz.
The factors can already contain the indicator of a symmetric good-pair set. -/
theorem integrated_modes_of_rows {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (a c : X × X → ℝ) (F : X → ℝ)
    (ha : Measurable a) (hc : Measurable c)
    (hai : Integrable (fun p => a p ^ 2) (μ.prod μ))
    (hci : Integrable (fun p => c p ^ 2) (μ.prod μ))
    (hFi : Integrable F μ) (hF0 : ∀ x, 0 ≤ F x)
    {E χ kE ko ks : ℝ} (hE : 0 ≤ E) (hχ : 0 ≤ χ)
    (hkE : 0 ≤ kE) (hko : 0 ≤ ko) (hks : 0 ≤ ks)
    (hrowA : ∀ x, ∫ y, a (x, y) ^ 2 ∂μ ≤ E * F x)
    (hrowC : ∀ x, ∫ y, c (x, y) ^ 2 ∂μ ≤ E * χ * F x) :
    kE * (∫ p, a p * a p.swap ∂μ.prod μ) +
      ko * ((∫ p, c p * a p.swap ∂μ.prod μ) + ∫ p, a p * c p.swap ∂μ.prod μ) +
      ks * (∫ p, c p * c p.swap ∂μ.prod μ) ≤
      (E * ∫ x, F x ∂μ) * (kE + 2 * ko * √χ + ks * χ) := by
  have hAF : (∫ p, a p ^ 2 ∂μ.prod μ) ≤ E * ∫ x, F x ∂μ := by
    rw [integral_prod _ hai, ← integral_const_mul]
    exact integral_mono hai.integral_prod_left (hFi.const_mul E) hrowA
  have hCF : (∫ p, c p ^ 2 ∂μ.prod μ) ≤ (E * ∫ x, F x ∂μ) * χ := by
    have h := integral_mono hci.integral_prod_left (hFi.const_mul (E * χ)) hrowC
    rw [← integral_prod _ hci, integral_const_mul] at h
    convert h using 1 <;> ring
  apply integrated_four_modes (μ.prod μ) a (fun p => a p.swap) c (fun p => c p.swap)
    ha (ha.comp measurable_swap) hc (hc.comp measurable_swap)
    hai hai.swap hci hci.swap
    (mul_nonneg hE (integral_nonneg hF0)) hχ hkE hko hks hAF
  · rw [integral_prod_swap (fun p => a p ^ 2)]
    exact hAF
  · exact hCF
  · rw [integral_prod_swap (fun p => c p ^ 2)]
    exact hCF

end BstLean.Part208
