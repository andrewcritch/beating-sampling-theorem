import BstLean.Part154MFv

/-! Pair-complement integration under one fixed input distribution. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set

/-- Integrate the regular remainder and the two exceptional input indices.
The product measure contains input indices; all network data stay fixed. -/
theorem pair_remainder {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : Ω → ℝ} {Q R : Ω × Ω → ℝ} {B : Set Ω}
    {C H s b : ℝ} (hσi : Integrable σ μ) (hσ0 : ∀ x, 0 ≤ σ x)
    (hB : MeasurableSet B) (hQi : Integrable Q (μ.prod μ)) (hQ0 : ∀ p, 0 ≤ Q p)
    (hRm : AEStronglyMeasurable R (μ.prod μ)) (hR0 : ∀ p, 0 ≤ R p)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hb : 0 ≤ b)
    (hQ : (∫ p, Q p ∂μ.prod μ) ≤ H)
    (hMean : (∫ x, σ x ∂μ) ≤ s) (hBad : (∫ x in B, σ x ∂μ) ≤ b)
    (hRegular : ∀ p, p.1 ∉ B → p.2 ∉ B → R p ≤ C * Q p)
    (hGlobal : ∀ p, R p ≤ σ p.1 * σ p.2 / 8) :
    Integrable R (μ.prod μ) ∧ (∫ p, R p ∂μ.prod μ) ≤ C * H + s * b / 4 := by
  classical
  let σB := B.indicator σ
  have hBi : Integrable σB μ := hσi.indicator hB
  have hB0 : ∀ x, 0 ≤ σB x := indicator_nonneg (fun x _ => hσ0 x)
  have hU1 : Integrable (fun p : Ω × Ω => C * Q p) (μ.prod μ) := hQi.const_mul _
  have hU2 : Integrable (fun p : Ω × Ω => σB p.1 * σ p.2) (μ.prod μ) :=
    hBi.mul_prod hσi
  have hU3 : Integrable (fun p : Ω × Ω => σ p.1 * σB p.2) (μ.prod μ) :=
    hσi.mul_prod hBi
  have hBound : ∀ p : Ω × Ω, R p ≤ C * Q p +
      (σB p.1 * σ p.2 + σ p.1 * σB p.2) / 8 := by
    intro p
    have hCQ := mul_nonneg hC (hQ0 p)
    have h1 := mul_nonneg (hB0 p.1) (hσ0 p.2)
    have h2 := mul_nonneg (hσ0 p.1) (hB0 p.2)
    by_cases hp1 : p.1 ∈ B
    · have he : σB p.1 = σ p.1 := indicator_of_mem hp1 σ
      rw [he]
      linarith [hGlobal p]
    by_cases hp2 : p.2 ∈ B
    · have he : σB p.2 = σ p.2 := indicator_of_mem hp2 σ
      rw [he]
      linarith [hGlobal p]
    have he1 : σB p.1 = 0 := indicator_of_notMem hp1 σ
    have he2 : σB p.2 = 0 := indicator_of_notMem hp2 σ
    simp only [he1, he2, zero_mul, mul_zero, add_zero, zero_div]
    exact hRegular p hp1 hp2
  have hUi := hU1.add ((hU2.add hU3).div_const 8)
  have hRi : Integrable R (μ.prod μ) := hUi.mono' hRm (ae_of_all _ fun p => by
    rw [Real.norm_of_nonneg (hR0 p)]; exact hBound p)
  have heB : ∫ x, σB x ∂μ = ∫ x in B, σ x ∂μ := integral_indicator hB
  have hBad' : (∫ x, σB x ∂μ) ≤ b := by rw [heB]; exact hBad
  have hProd : (∫ x, σB x ∂μ) * (∫ x, σ x ∂μ) ≤ b * s :=
    mul_le_mul hBad' hMean (integral_nonneg hσ0) hb
  refine ⟨hRi, ?_⟩
  have hi := integral_mono hRi hUi hBound
  simp only [Pi.add_apply] at hi
  rw [integral_add (μ := μ.prod μ) (f := fun p : Ω × Ω => C * Q p)
      (g := fun p : Ω × Ω => (σB p.1 * σ p.2 + σ p.1 * σB p.2) / 8)
      hU1 ((hU2.add hU3).div_const 8), integral_const_mul,
    integral_div, integral_add (μ := μ.prod μ) (f := fun p : Ω × Ω => σB p.1 * σ p.2)
      (g := fun p : Ω × Ω => σ p.1 * σB p.2) hU2 hU3,
    integral_prod_mul, integral_prod_mul] at hi
  have hCQ := mul_le_mul_of_nonneg_left hQ hC
  have hProd' : (∫ x, σ x ∂μ) * (∫ x, σB x ∂μ) ≤ b * s := by
    rw [mul_comm]; exact hProd
  linarith

open BstLean.Part154

/-- Apply the pair reduction to the existing projected covariance kernel. -/
theorem MF_remainder_of_regular_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {m : ℕ} {f : Ω → Fin m → ℝ}
    {L pg C b : ℝ} (H : MFHyp μ f L pg) {B : Set Ω} (hB : MeasurableSet B)
    {R : Ω × Ω → ℝ} (hRm : AEStronglyMeasurable R (μ.prod μ))
    (hR0 : ∀ p, 0 ≤ R p) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hBad : (∫ x in B, sgF μ f x ∂μ) ≤ b)
    (hRegular : ∀ p, p.1 ∉ B → p.2 ∉ B → R p ≤ C * ccF μ f p ^ 2)
    (hGlobal : ∀ p, R p ≤ sgF μ f p.1 * sgF μ f p.2 / 8) :
    Integrable R (μ.prod μ) ∧
      (∫ p, R p ∂μ.prod μ) ≤ C * hsF μ f + sF μ f * b / 4 :=
  pair_remainder H.int_sg (fun _ => BstLean.Part153.nrm_nonneg _) hB H.F4c.1
    (fun _ => sq_nonneg _) hRm hR0 hC H.sF_pos.1.le hb H.F4c.2 H.sig_int.2.1
    hBad hRegular hGlobal

#print axioms MF_remainder_of_regular_bound
#print axioms pair_remainder
end BstLean.Part194
