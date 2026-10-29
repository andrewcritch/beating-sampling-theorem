import BstLean.Part242Integral
import BstLean.Part207HQ

/-! The integrated HQ cubic uses the improved A and D constants. -/
namespace BstLean.Part242
open MeasureTheory Real
open scoped ENNReal

noncomputable def mixL3 (n : ℕ) (ε A D : ℝ) : ℝ :=
  (n * A / 4 + (1 - ε) * D / 2) / (1 - ε) ^ 2 +
    (sqrt (A * D) + sqrt ((n : ℝ) / 2) * A) / (1 - ε)

lemma sqrt_product_majorant {A D v w : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hv : 0 ≤ v) (hw : 0 ≤ w) :
    sqrt (v * w) ≤ D / (2 * sqrt (A * D)) * v + A / (2 * sqrt (A * D)) * w := by
  have hz : 0 < sqrt (A * D) := sqrt_pos.mpr (mul_pos hA hD)
  have h1 := sq_sqrt (mul_nonneg hv hw)
  have h2 := sq_sqrt (mul_pos hA hD).le
  have hnum : 0 ≤ D * v + A * w := by positivity
  have hle : 2 * sqrt (A * D) * sqrt (v * w) ≤ D * v + A * w := by
    nlinarith [sq_nonneg (D * v - A * w), sqrt_nonneg (v * w)]
  have hh := (le_div_iff₀ (show 0 < 2 * sqrt (A * D) by positivity)).mpr
    (show sqrt (v * w) * (2 * sqrt (A * D)) ≤ D * v + A * w by nlinarith [hle])
  exact hh.trans_eq (by ring)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem sqrt_product_L3 {v w : X → ℝ} {A D : ℝ} (hA : 0 < A) (hD : 0 < D)
    (hv : LBound μ 3 v A) (hw : LBound μ 3 w D)
    (hv0 : ∀ x, 0 ≤ v x) (hw0 : ∀ x, 0 ≤ w x) :
    LBound μ 3 (fun x => sqrt (v x * w x)) (sqrt (A * D)) := by
  have hs := (hv.scale (by norm_num : (3 : ℕ) ≠ 0)
    (show 0 ≤ D / (2 * sqrt (A * D)) by positivity)).add (by norm_num)
    (hw.scale (by norm_num : (3 : ℕ) ≠ 0)
      (show 0 ≤ A / (2 * sqrt (A * D)) by positivity))
  have hz : 0 < sqrt (A * D) := sqrt_pos.mpr (mul_pos hA hD)
  have he : D / (2 * sqrt (A * D)) * A + A / (2 * sqrt (A * D)) * D = sqrt (A * D) := by
    calc
      _ = (A * D) / sqrt (A * D) := by ring
      _ = sqrt (A * D) := (div_eq_iff hz.ne').mpr (by
        rw [← sq, sq_sqrt (mul_pos hA hD).le])
  have hs' : LBound μ 3
      (fun x => D / (2 * sqrt (A * D)) * v x + A / (2 * sqrt (A * D)) * w x)
      (sqrt (A * D)) := by simpa only [he, Nat.cast_ofNat] using hs
  apply hs'.mono ((hv.measurable.mul hw.measurable).sqrt)
  exact Filter.Eventually.of_forall fun x => by
    have hvp := hv0 x
    have hwp := hw0 x
    rw [abs_of_nonneg (sqrt_nonneg _), abs_of_nonneg (by positivity)]
    exact sqrt_product_majorant hA hD (hv0 x) (hw0 x)

theorem HQ_L3 (n : ℕ) {ε A D : ℝ} (hε : ε < 1) (hA : 0 < A) (hD : 0 < D)
    {v w : X → ℝ} (hv : LBound μ 3 v A) (hw : LBound μ 3 w D)
    (hv0 : ∀ x, 0 ≤ v x) (hw0 : ∀ x, 0 ≤ w x) :
    LBound μ 3 (fun x => BstLean.Part207.hqL n ε (v x) (w x)) (mixL3 n ε A D) := by
  have h1 := hv.scale (by norm_num : (3 : ℕ) ≠ 0)
    (show 0 ≤ (n : ℝ) / (4 * (1 - ε) ^ 2) by positivity)
  have h2 := hw.scale (by norm_num : (3 : ℕ) ≠ 0)
    (show 0 ≤ 1 / (2 * (1 - ε)) by positivity)
  have h3 := (sqrt_product_L3 hA hD hv hw hv0 hw0).scale (by norm_num : (3 : ℕ) ≠ 0)
    (show 0 ≤ (1 - ε)⁻¹ by positivity)
  have h4 := hv.scale (by norm_num : (3 : ℕ) ≠ 0)
    (show 0 ≤ sqrt ((n : ℝ) / 2) / (1 - ε) by positivity)
  have hs := ((h1.add (by norm_num) h2).add (by norm_num) h3).add (by norm_num) h4
  convert hs using 1
  · funext x
    unfold BstLean.Part207.hqL
    ring
  · unfold mixL3
    field_simp <;> ring

theorem HQ_integral {C L : X → ℝ} {Cbound Lbound : ℝ}
    (iC : Integrable C μ) (hC : ∫ x, C x ∂μ ≤ Cbound)
    (hL : LBound μ 3 L Lbound) (hL0 : ∀ x, 0 ≤ L x)
    {rootError : X → ℝ}
    (hpoint : ∀ᵐ x ∂μ, rootError x ^ 2 ≤ C x / 4 + 6 * L x ^ 3) :
    ∫ x, rootError x ^ 2 ∂μ ≤ Cbound / 4 + 6 * Lbound ^ 3 := by
  obtain ⟨iL, bL⟩ := hL.nonnegIntegral (by norm_num : (3 : ℕ) ≠ 0) hL0
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg (rootError x))
    ((iC.div_const 4).add (iL.const_mul 6)) hpoint
  simp only [Pi.add_apply] at hm
  rw [integral_add (iC.div_const 4) (iL.const_mul 6), integral_div, integral_const_mul] at hm
  exact hm.trans (add_le_add (div_le_div_of_nonneg_right hC (by norm_num))
    (mul_le_mul_of_nonneg_left bL (by norm_num)))

end BstLean.Part242
