import BstLean.Part242Deficit
import BstLean.Part169Scale

/-! Improved integrated scale bounds preserve the stored program floor. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

noncomputable def syScale (n : ℕ) (aw af F8 Γ Cv d : ℝ) : ℝ :=
  (aw + 2 * F8 * af + af ^ 2 / n) * Γ + Cv / d

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem SY_scale (n : ℕ) (hn : 0 < n) (hmass : μ univ ≤ 1)
    {γ d aw af F8 Γ Cv : ℝ} (hγ : 0 < γ) (hd : 1 / 5 ≤ d)
    {fb ft wb wt V : X → ℝ}
    (mfb : Measurable fb) (mft : Measurable ft) (mwb : Measurable wb)
    (mwt : Measurable wt) (mV : Measurable V)
    (hfloor : ∀ᵐ x ∂μ, d ≤ wb x - fb x ^ 2 - V x)
    (hW : LBound μ 8 (fun x => (n : ℝ) * (wb x - wt x)) aw)
    (hF : LBound μ 8 (fun x => (n : ℝ) * (fb x - ft x)) af)
    (hf : LBound μ 8 fb F8)
    (hR : LBound μ 4 (fun x => 1 / (wb x - fb x ^ 2 - V x)) Γ)
    (hV : LBound μ 2 (fun x => (n : ℝ) * V x) Cv) :
    LBound μ 2
      (fun x => (n : ℝ) * (γ * max (1 / 5) (wt x - ft x ^ 2) /
        (γ * (wb x - fb x ^ 2 - V x)) - 1)) (syScale n aw af F8 Γ Cv d) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : 0 < d := by linarith
  let R : X → ℝ := fun x => 1 / (wb x - fb x ^ 2 - V x)
  let df : X → ℝ := fun x => (n : ℝ) * (fb x - ft x)
  let dw : X → ℝ := fun x => (n : ℝ) * (wb x - wt x)
  have hw2 : LBound μ 2 (fun x => |dw x * R x|) (aw * Γ) := by
    have h := (SY_location_div hW hR).lower (by norm_num) eighthirds_ne_top
      two_le_eighthirds hmass
    simpa only [dw, R] using h.mono h.measurable.abs
      (Filter.Eventually.of_forall fun x => by simp)
  have hp2 : LBound μ 2 (fun x => 2 * |fb x * (df x * R x)|)
      (2 * (F8 * (af * Γ))) := by
    have h := SY_location_product hf hF hR
    exact (h.mono h.measurable.abs
      (Filter.Eventually.of_forall fun x => by simp)).scale (by norm_num) (by norm_num)
  have hsq : LBound μ 4 (fun x => df x ^ 2) (af ^ 2) := by
    simpa only [Nat.cast_ofNat] using LBound.ofMoment (by norm_num : (4 : ℕ) ≠ 0)
      ((hF.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 4) (r := 2))
  have hsq2 : LBound μ 2 (fun x => (n : ℝ)⁻¹ * (df x ^ 2 * R x))
      ((n : ℝ)⁻¹ * (af ^ 2 * Γ)) :=
    (hsq.mul (r := 2) hR).scale (by norm_num) (by positivity)
  have hv2 : LBound μ 2 (fun x => d⁻¹ * |(n : ℝ) * V x|) (d⁻¹ * Cv) :=
    (hV.mono hV.measurable.abs
      (Filter.Eventually.of_forall fun x => by simp)).scale (by norm_num) (by positivity)
  have hsum := ((hw2.add (by norm_num) hp2).add (by norm_num) hsq2).add (by norm_num) hv2
  have hsum' : LBound μ 2
      (fun x => |dw x * R x| + 2 * |fb x * (df x * R x)| +
        (n : ℝ)⁻¹ * (df x ^ 2 * R x) + d⁻¹ * |(n : ℝ) * V x|)
      (syScale n aw af F8 Γ Cv d) := by
    convert hsum using 1
    unfold syScale
    ring
  have mS : Measurable
      (fun x => (n : ℝ) * (γ * max (1 / 5) (wt x - ft x ^ 2) /
        (γ * (wb x - fb x ^ 2 - V x)) - 1)) := by
    fun_prop
  apply hsum'.mono mS
  filter_upwards [hfloor] with x hx
  have hy : 0 < wb x - fb x ^ 2 - V x := hd0.trans_le hx
  have hr : 0 < R x := one_div_pos.mpr hy
  have hb := BstLean.Part169.scale_pt (wt := wt x) (ft := ft x) hγ
    (hd.trans hx) (le_refl (γ * (wb x - fb x ^ 2 - V x)))
  have hv : |V x| / (wb x - fb x ^ 2 - V x) ≤ |V x| / d :=
    div_le_div_of_nonneg_left (abs_nonneg _) hd0 hx
  have hb' := mul_le_mul_of_nonneg_left hb hnR.le
  have hs0 : 0 ≤ |dw x * R x| + 2 * |fb x * (df x * R x)| +
      (n : ℝ)⁻¹ * (df x ^ 2 * R x) + d⁻¹ * |(n : ℝ) * V x| := by positivity
  rw [abs_mul, abs_of_pos hnR]
  rw [abs_of_nonneg hs0]
  dsimp [dw, df, R] at *
  simp only [abs_mul, abs_of_pos hnR, abs_of_pos (one_div_pos.mpr hy)]
  calc
    _ ≤ (n : ℝ) * ((|wb x - wt x| + 2 * |fb x| * |fb x - ft x| +
        (fb x - ft x) ^ 2 + |V x|) / (wb x - fb x ^ 2 - V x)) := hb'
    _ ≤ (n : ℝ) * ((|wb x - wt x| + 2 * |fb x| * |fb x - ft x| +
        (fb x - ft x) ^ 2) / (wb x - fb x ^ 2 - V x) + |V x| / d) := by
      gcongr
      rw [add_div]
      exact add_le_add le_rfl hv
    _ = _ := by field_simp

end BstLean.Part242
