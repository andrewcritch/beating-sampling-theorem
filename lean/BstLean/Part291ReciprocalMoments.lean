import BstLean.Part291RW
import BstLean.Part291EnergyMoment

namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part188

/-- Positive square deficit moments follow from centered moments, with the
same mean on the original measure. No law is changed by the reciprocal weight. -/
theorem square_deficit_moment {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f) {p : ℕ} (hp : 1 ≤ p)
    {mu m A B : ℝ} (hmu : 0 ≤ mu) (hm : mu ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hi1 : Integrable (fun x => |f x - mu| ^ p) μ)
    (hi2 : Integrable (fun x => |f x - mu| ^ (2 * p)) μ)
    (h1 : (∫ x, |f x - mu| ^ p ∂μ) ≤ A ^ p)
    (h2 : (∫ x, |f x - mu| ^ (2 * p) ∂μ) ≤ B ^ (2 * p)) :
    Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ p) μ ∧
    (∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ p ∂μ) ≤ (2 * m * A + B ^ 2) ^ p := by
  have hm0 : 0 ≤ m := hmu.trans hm
  have hX : Measurable (fun x => 2 * m * |f x - mu|) :=
    (hf.sub measurable_const).abs.const_mul _
  have hY : Measurable (fun x => |f x - mu| ^ 2) :=
    ((hf.sub measurable_const).abs.pow_const 2)
  have hiX : Integrable (fun x => (2 * m * |f x - mu|) ^ p) μ := by
    simpa only [mul_pow] using hi1.const_mul ((2 * m) ^ p)
  have hiY : Integrable (fun x => (|f x - mu| ^ 2) ^ p) μ := by
    simpa only [pow_mul] using hi2
  have hXb : (∫ x, (2 * m * |f x - mu|) ^ p ∂μ) ≤ (2 * m * A) ^ p := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ p * m ^ p)
  have hYb : (∫ x, (|f x - mu| ^ 2) ^ p ∂μ) ≤ (B ^ 2) ^ p := by
    simpa only [pow_mul] using h2
  have hsum := BstLean.Part209.moment_add hX hY (fun _ => by positivity)
    (fun _ => sq_nonneg _) hp (by positivity) (sq_nonneg B) hiX hiY hXb hYb
  have hpt : ∀ x, (max (f x ^ 2 - m ^ 2) 0) ^ p ≤
      (2 * m * |f x - mu| + |f x - mu| ^ 2) ^ p := by
    intro x
    apply pow_le_pow_left₀ (le_max_right _ _)
    simpa only [sq_abs] using (square_deficit_bound (f := f x) hmu hm)
  have hi : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ p) μ := by
    apply hsum.1.mono' ((((hf.pow_const 2).sub measurable_const).max measurable_const).pow_const p).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt x
  exact ⟨hi, (integral_mono hi hsum.1 hpt).trans hsum.2⟩

theorem reciprocalExcess_moment2 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Measurable f) {a d m D2 D4 : ℝ}
    (hd : 0 < d) (hY : d < a - m ^ 2) (hD2 : 0 ≤ D2) (hD4 : 0 ≤ D4)
    (hi2 : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ 2) μ)
    (hi4 : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ 4) μ)
    (h2 : (∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ 2 ∂μ) ≤ D2 ^ 2)
    (h4 : (∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ 4 ∂μ) ≤ D4 ^ 4) :
    Integrable (fun x => reciprocalExcess a d m (f x) ^ 2) μ ∧
    (∫ x, reciprocalExcess a d m (f x) ^ 2 ∂μ) ≤
      (D2 / (a - m ^ 2) ^ 2 + D4 ^ 2 / (d * (a - m ^ 2) ^ 2)) ^ 2 := by
  have hY0 : 0 < a - m ^ 2 := hd.trans hY
  let Z := fun x => max (f x ^ 2 - m ^ 2) 0
  have hz : Measurable Z := ((hf.pow_const 2).sub measurable_const).max measurable_const
  have hz0 : ∀ x, 0 ≤ Z x := fun _ => le_max_right _ _
  have hX := hz.div_const ((a - m ^ 2) ^ 2)
  have hZ := (hz.pow_const 2).div_const (d * (a - m ^ 2) ^ 2)
  have hix : Integrable (fun x => (Z x / (a - m ^ 2) ^ 2) ^ 2) μ := by
    simpa only [div_pow] using hi2.div_const (((a - m ^ 2) ^ 2) ^ 2)
  have hiz : Integrable (fun x => (Z x ^ 2 / (d * (a - m ^ 2) ^ 2)) ^ 2) μ := by
    simpa only [div_pow, ← pow_mul] using hi4.div_const ((d * (a - m ^ 2) ^ 2) ^ 2)
  have hx : (∫ x, (Z x / (a - m ^ 2) ^ 2) ^ 2 ∂μ) ≤ (D2 / (a - m ^ 2) ^ 2) ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
    exact div_le_div_of_nonneg_right h2 (by positivity)
  have hz' : (∫ x, (Z x ^ 2 / (d * (a - m ^ 2) ^ 2)) ^ 2 ∂μ) ≤
      (D4 ^ 2 / (d * (a - m ^ 2) ^ 2)) ^ 2 := by
    simp_rw [div_pow, ← pow_mul]
    rw [integral_div]
    exact div_le_div_of_nonneg_right h4 (by positivity)
  exact BstLean.Part209.moment_add hX hZ (fun x => by positivity) (fun x => by positivity)
    (by norm_num) (by positivity) (by positivity) hix hiz hx hz'

end BstLean.BlueprintLow
