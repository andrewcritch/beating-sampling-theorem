import BstLean.Part208Tangential

/-! Part 208: restrict the overlap denominator before extending the numerator. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix Set
open BstLean.Part130 BstLean.Part182

/-- The row reduction uses the second moment on the larger input set.
The pair set can depend on both Agent matrices. -/
theorem restricted_tangent_row {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (_hn : 2 ≤ n) (u x f : Fin n → ℝ) (x' : X → Fin n → ℝ) (w : X → ℝ)
    (Ω H : Set X) (hHΩ : H ⊆ Ω)
    (hu : normSq u = 1) (hx : normSq x = 1) (hf : x ⬝ᵥ f = 0)
    {cp sp sm E : ℝ} (hcp : cp ^ 2 < 1) (hsp : 0 ≤ sp) (hE : 0 ≤ E)
    (hsm : sm ≤ (u ⬝ᵥ x) ^ 2) (hw : ∀ z, 0 ≤ w z)
    (hc : ∀ z ∈ H, (x ⬝ᵥ x' z) ^ 2 ≤ cp ^ 2)
    (hiH : Integrable (H.indicator (fun z => w z * (eTan x (x' z) ⬝ᵥ f) ^ 2)) μ)
    (hiΩ : Integrable (Ω.indicator (fun z => w z * (x' z ⬝ᵥ f) ^ 2)) μ)
    (hmoment : (∫ z, Ω.indicator (fun z => w z * (x' z ⬝ᵥ f) ^ 2) z ∂μ) ≤
      E * (sp * (u ⬝ᵥ f) ^ 2 + normSq f / ((n : ℝ) - 1))) :
    (∫ z, H.indicator (fun z => w z * (eTan x (x' z) ⬝ᵥ f) ^ 2) z ∂μ) ≤
      E * ((sp * (1 - sm) + 1 / ((n : ℝ) - 1)) / (1 - cp ^ 2)) * normSq f := by
  have hd : 0 < 1 - cp ^ 2 := by linarith
  have hpt : ∀ z,
      H.indicator (fun z => w z * (eTan x (x' z) ⬝ᵥ f) ^ 2) z ≤
        Ω.indicator (fun z => w z * (x' z ⬝ᵥ f) ^ 2) z / (1 - cp ^ 2) := by
    intro z
    by_cases hz : z ∈ H
    · rw [indicator_of_mem hz, indicator_of_mem (hHΩ hz)]
      have h := mul_le_mul_of_nonneg_left (tangent_pair_sq hf hcp (hc z hz)) (hw z)
      simpa only [mul_div_assoc] using h
    · rw [indicator_of_notMem hz]
      exact div_nonneg (indicator_nonneg (fun z _ => mul_nonneg (hw z) (sq_nonneg _)) z) hd.le
  have hi := integral_mono hiH (hiΩ.div_const (1 - cp ^ 2)) hpt
  rw [integral_div] at hi
  have hf2 := tangent_centre_sq hu hx hf
  have hf3 : (u ⬝ᵥ f) ^ 2 ≤ (1 - sm) * normSq f := by
    exact hf2.trans (mul_le_mul_of_nonneg_right (by linarith) (normSq_nonneg f))
  calc
    _ ≤ (∫ z, Ω.indicator (fun z => w z * (x' z ⬝ᵥ f) ^ 2) z ∂μ) / (1 - cp ^ 2) := hi
    _ ≤ (E * (sp * (u ⬝ᵥ f) ^ 2 + normSq f / ((n : ℝ) - 1))) / (1 - cp ^ 2) :=
      div_le_div_of_nonneg_right hmoment hd.le
    _ ≤ (E * (sp * ((1 - sm) * normSq f) + normSq f / ((n : ℝ) - 1))) / (1 - cp ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hf3 hsp) le_rfl) hE) hd.le
    _ = _ := by ring

end BstLean.Part208
