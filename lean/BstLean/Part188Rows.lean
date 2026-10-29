import BstLean.Part188Schur
import BstLean.Part188WF

namespace BstLean.Part188

open MeasureTheory Real

/-- A dependent density changes a bounded row by its positive excess in L2. -/
theorem dependent_row_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (w q g : X → ℝ)
    {q0 C A B Delta : ℝ} (hq0 : 0 ≤ q0) (hC : 0 ≤ C)
    (hw0 : ∀ x, 0 ≤ w x) (hg0 : ∀ x, 0 ≤ g x) (hgC : ∀ x, g x ≤ C)
    (hiwg : Integrable (fun x => w x * g x) μ)
    (hiwqg : Integrable (fun x => w x * q x * g x) μ)
    (hiwD : Integrable (fun x => w x * max (q x - q0) 0) μ)
    (hiwDg : Integrable (fun x => w x * max (q x - q0) 0 * g x) μ)
    (hiw2 : Integrable (fun x => w x ^ 2) μ)
    (hiD2 : Integrable (fun x => (max (q x - q0) 0) ^ 2) μ)
    (hA : ∫ x, w x * g x ∂μ ≤ A)
    (hB : √(∫ x, w x ^ 2 ∂μ) ≤ B)
    (hDelta : √(∫ x, (max (q x - q0) 0) ^ 2 ∂μ) ≤ Delta) :
    ∫ x, w x * q x * g x ∂μ ≤ q0 * A + C * B * Delta := by
  have hcs := BstLean.Part170.int_cs hiw2 hiD2 hiwD
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans hB
  have hDelta0 : 0 ≤ Delta := (Real.sqrt_nonneg _).trans hDelta
  have hcs' : ∫ x, w x * max (q x - q0) 0 ∂μ ≤ B * Delta :=
    hcs.trans (mul_le_mul hB hDelta (Real.sqrt_nonneg _) hB0)
  have hg := integral_mono hiwDg (hiwD.const_mul C) (fun x => by
    have h := mul_le_mul_of_nonneg_left (hgC x)
      (mul_nonneg (hw0 x) (le_max_right (q x - q0) 0))
    simpa only [mul_comm C, mul_assoc] using h)
  rw [integral_const_mul] at hg
  have hpt : ∀ x, w x * q x * g x ≤ q0 * (w x * g x) +
      w x * max (q x - q0) 0 * g x := by
    intro x
    have hq : q x ≤ q0 + max (q x - q0) 0 := by
      have := le_max_left (q x - q0) 0
      linarith
    have h := mul_le_mul_of_nonneg_left hq (mul_nonneg (hw0 x) (hg0 x))
    nlinarith only [h]
  have h := integral_mono hiwqg ((hiwg.const_mul q0).add hiwDg) hpt
  dsimp only [Pi.add_apply] at h
  rw [integral_add (hiwg.const_mul q0) hiwDg, integral_const_mul] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hA hq0)
    (hg.trans (by have := mul_le_mul_of_nonneg_left hcs' hC; nlinarith only [this])))

end BstLean.Part188
