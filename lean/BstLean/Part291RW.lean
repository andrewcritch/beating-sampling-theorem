import BstLean.Part188RW
import BstLean.Part170FlQ

/-! RW with a constant term and a dependent positive excess.
Only the constant term uses the original, unweighted first moment. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part188

theorem rw_dependent_average {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (q e w : X → ℝ)
    {c B D R : ℝ} (hc : 0 ≤ c) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hw : ∀ x, 0 ≤ w x) (hq : ∀ x, q x ≤ c + e x)
    (hiw : Integrable w μ) (hiqw : Integrable (fun x => q x * w x) μ)
    (hiew : Integrable (fun x => e x * w x) μ)
    (hie2 : Integrable (fun x => e x ^ 2) μ)
    (hiw2 : Integrable (fun x => w x ^ 2) μ)
    (hB : ∫ x, w x ∂μ ≤ B)
    (hDe : ∫ x, e x ^ 2 ∂μ ≤ D ^ 2) (hRw : ∫ x, w x ^ 2 ∂μ ≤ R ^ 2) :
    ∫ x, q x * w x ∂μ ≤ c * B + D * R := by
  have hcs := BstLean.Part170.int_cs hie2 hiw2 hiew
  have hds : √(∫ x, e x ^ 2 ∂μ) ≤ D := sqrt_le_iff.mpr ⟨hD, hDe⟩
  have hrs : √(∫ x, w x ^ 2 ∂μ) ≤ R := sqrt_le_iff.mpr ⟨hR, hRw⟩
  have hex : ∫ x, e x * w x ∂μ ≤ D * R :=
    hcs.trans (mul_le_mul hds hrs (sqrt_nonneg _) hD)
  have hpt : ∀ x, q x * w x ≤ c * w x + e x * w x := by
    intro x
    calc
      _ ≤ (c + e x) * w x := mul_le_mul_of_nonneg_right (hq x) (hw x)
      _ = _ := by ring
  have h := integral_mono hiqw ((hiw.const_mul c).add hiew) hpt
  simp only [Pi.add_apply] at h
  rw [integral_add (hiw.const_mul c) hiew, integral_const_mul] at h
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hB hc) hex)

noncomputable def reciprocalExcess (a d m f : ℝ) : ℝ :=
  max (f ^ 2 - m ^ 2) 0 / (a - m ^ 2) ^ 2 +
    (max (f ^ 2 - m ^ 2) 0) ^ 2 / (d * (a - m ^ 2) ^ 2)

theorem reciprocalExcess_nonneg {a d m f : ℝ} (hd : 0 < d) :
    0 ≤ reciprocalExcess a d m f := by
  unfold reciprocalExcess
  positivity

theorem reciprocalExcess_bound {a d m f : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2) :
    weightSq a d f ≤ 1 / (a - m ^ 2) + reciprocalExcess a d m f := by
  have h := reciprocal_weight_bound (f := f) hd hY
  simpa only [reciprocalExcess, add_assoc] using h

/-- The radius moment and the tangential moment use the same estimate with
different w. There is no rotation-invariance hypothesis on the scalar weight. -/
theorem rw_capped_average {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f w : X → ℝ)
    {a d m B D R : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2)
    (hD : 0 ≤ D) (hR : 0 ≤ R) (hw : ∀ x, 0 ≤ w x)
    (hiw : Integrable w μ)
    (hiqw : Integrable (fun x => weightSq a d (f x) * w x) μ)
    (hiew : Integrable (fun x => reciprocalExcess a d m (f x) * w x) μ)
    (hie2 : Integrable (fun x => reciprocalExcess a d m (f x) ^ 2) μ)
    (hiw2 : Integrable (fun x => w x ^ 2) μ)
    (hB : ∫ x, w x ∂μ ≤ B)
    (hDe : ∫ x, reciprocalExcess a d m (f x) ^ 2 ∂μ ≤ D ^ 2)
    (hRw : ∫ x, w x ^ 2 ∂μ ≤ R ^ 2) :
    ∫ x, weightSq a d (f x) * w x ∂μ ≤ B / (a - m ^ 2) + D * R := by
  have hY0 : 0 < a - m ^ 2 := hd.trans hY
  have h := rw_dependent_average μ (fun x => weightSq a d (f x))
    (fun x => reciprocalExcess a d m (f x)) w (c := 1 / (a - m ^ 2))
    (by positivity) hD hR hw (fun _ => reciprocalExcess_bound hd hY)
    hiw hiqw hiew hie2 hiw2 hB hDe hRw
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

end BstLean.BlueprintLow
