import BstLean.Part177EnMom

/-! Nonnegative moment transfer keeps both layers and every input under shared weights. -/
namespace BstLean.Part222
open MeasureTheory
open scoped ENNReal

/-- An integrable outer bound supplies product integrability and the product moment. -/
theorem product_moment_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X × Y → ℝ) (hf : Measurable f) (h0 : ∀ p, 0 ≤ f p)
    (hi : ∀ x, Integrable (fun y => f (x,y)) ν)
    (b : X → ℝ) (hb : Integrable b μ) (hb0 : ∀ x, 0 ≤ b x)
    (hbound : ∀ x, (∫ y, f (x,y) ∂ν) ≤ b x) :
    Integrable f (μ.prod ν) ∧ (∫ p, f p ∂μ.prod ν) ≤ ∫ x, b x ∂μ := by
  have hL : (∫⁻ p, ENNReal.ofReal (f p) ∂μ.prod ν) ≤
      ENNReal.ofReal (∫ x, b x ∂μ) := by
    rw [lintegral_prod _ hf.ennreal_ofReal.aemeasurable]
    calc (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x,y)) ∂ν ∂μ)
        ≤ ∫⁻ x, ENNReal.ofReal (b x) ∂μ := by
          apply lintegral_mono
          intro x
          change (∫⁻ y, ENNReal.ofReal (f (x,y)) ∂ν) ≤ ENNReal.ofReal (b x)
          rw [← ofReal_integral_eq_lintegral_ofReal (hi x)
            (Filter.Eventually.of_forall fun y => h0 (x,y))]
          exact ENNReal.ofReal_le_ofReal (hbound x)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hb
        (Filter.Eventually.of_forall hb0)).symm
  have hI : Integrable f (μ.prod ν) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h0)]
    exact hL.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall h0)] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hb0)).mp hL

/-- A pointwise weight moment bound transfers through an arbitrary fixed input distribution. -/
theorem averaged_moment_bound {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (ν : Measure W) (μ : Measure X) [SFinite ν] [IsProbabilityMeasure μ]
    (f : W → X → ℝ) (hf : Measurable (Function.uncurry f)) (h0 : ∀ a x, 0 ≤ f a x)
    (hi : ∀ a, Integrable (f a) μ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ x, Integrable (fun a => f a x) ν ∧ (∫ a, f a x ∂ν) ≤ B) :
    Integrable (fun a => ∫ x, f a x ∂μ) ν ∧
    (∫ a, ∫ x, f a x ∂μ ∂ν) ≤ B := by
  have hg : Measurable (fun p : X × W => f p.2 p.1) := hf.comp measurable_swap
  obtain ⟨hprod, hbound⟩ := product_moment_bound μ ν _ hg
    (fun p => h0 p.2 p.1) (fun x => (hw x).1) (fun _ => B)
    (integrable_const _) (fun _ => hB) (fun x => (hw x).2)
  have hswap : Integrable (Function.uncurry f) (ν.prod μ) :=
    hprod.swap
  refine ⟨hswap.integral_prod_left, ?_⟩
  calc (∫ a, ∫ x, f a x ∂μ ∂ν) = ∫ x, ∫ a, f a x ∂ν ∂μ :=
        integral_integral_swap hswap
    _ = ∫ p, f p.2 p.1 ∂μ.prod ν := (integral_prod _ hprod).symm
    _ ≤ ∫ x, B ∂μ := hbound
    _ = B := by simp

#print axioms product_moment_bound
#print axioms averaged_moment_bound
end BstLean.Part222
