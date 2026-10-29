import BstLean.Part242Holder

/-! SY2 changes integrated constants and keeps pointwise cutoffs separate. -/
namespace BstLean.Part242
open MeasureTheory Real
open scoped ENNReal

noncomputable def mixA (dw d Γ V η : ℝ) : ℝ :=
  4 * (1 + dw / sqrt d) ^ 2 * Γ * V / (1 - η)

noncomputable def mixD (n : ℕ) (χ Γ V η : ℝ) : ℝ :=
  n * χ * Γ * V / (1 - η)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The variance estimates use the same reciprocal norm at orders two and three. -/
theorem SY2_variance_constants {dw d Γ V η : ℝ} (hη : η < 1)
    {v R : X → ℝ} (hv4 : LBound μ 4 v V) (hv12 : LBound μ 12 v V)
    (hR : LBound μ 4 R Γ) :
    LBound μ 2 (fun x => (4 * (1 + dw / sqrt d) ^ 2 / (1 - η)) * (v x * R x))
      (mixA dw d Γ V η) ∧
    LBound μ 3 (fun x => (4 * (1 + dw / sqrt d) ^ 2 / (1 - η)) * (v x * R x))
      (mixA dw d Γ V η) := by
  obtain ⟨h2, h3⟩ := SY2_products hv4 hv12 hR
  have ha : 0 ≤ 4 * (1 + dw / sqrt d) ^ 2 / (1 - η) := by positivity
  have h2' := h2.scale (by norm_num : (2 : ℕ) ≠ 0) ha
  have h3' := h3.scale (by norm_num : (3 : ℕ) ≠ 0) ha
  have he : (4 * (1 + dw / sqrt d) ^ 2 / (1 - η)) * (V * Γ) =
      mixA dw d Γ V η := by unfold mixA; ring
  exact ⟨he ▸ h2', he ▸ h3'⟩

theorem SY2_location_constants (n : ℕ) {χ Γ V η : ℝ}
    (hχ : 0 ≤ χ) (hη : η < 1) {v R : X → ℝ}
    (hv4 : LBound μ 4 v V) (hv12 : LBound μ 12 v V) (hR : LBound μ 4 R Γ) :
    LBound μ 2 (fun x => ((n : ℝ) * χ / (1 - η)) * (v x * R x))
      (mixD n χ Γ V η) ∧
    LBound μ 3 (fun x => ((n : ℝ) * χ / (1 - η)) * (v x * R x))
      (mixD n χ Γ V η) := by
  obtain ⟨h2, h3⟩ := SY2_products hv4 hv12 hR
  have ha : 0 ≤ (n : ℝ) * χ / (1 - η) := by positivity
  have h2' := h2.scale (by norm_num : (2 : ℕ) ≠ 0) ha
  have h3' := h3.scale (by norm_num : (3 : ℕ) ≠ 0) ha
  have he : ((n : ℝ) * χ / (1 - η)) * (V * Γ) = mixD n χ Γ V η := by
    unfold mixD
    ring
  exact ⟨he ▸ h2', he ▸ h3'⟩

/-- Scalar pointwise bounds transfer the estimates without a new event. -/
theorem SY2_transfer {A B : ℝ} {major E : X → ℝ} {p : ℝ≥0∞}
    (hmajor : LBound μ p major A) (mE : Measurable E)
    (hE : ∀ᵐ x ∂μ, |E x| ≤ |major x|) : LBound μ p E A :=
  hmajor.mono mE hE

end BstLean.Part242
