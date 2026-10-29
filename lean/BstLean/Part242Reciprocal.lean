import BstLean.Part242Conditional
import BstLean.Part242Holder

/-! SY and SY2 keep distinct pointwise floors. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

noncomputable def reciprocalBound (d Y0 deficit : ℝ) : ℝ :=
  1 / Y0 + deficit / (d * Y0)

noncomputable def gammaY (d Y0 H μ0 g8 : ℝ) : ℝ :=
  reciprocalBound d Y0 (2 * H + g8 * (2 * μ0 + g8))

noncomputable def gMix (d Y0 H μ0 g8 η τ8 V : ℝ) : ℝ :=
  reciprocalBound d Y0 (2 * H + g8 * (2 * μ0 + g8) +
    sqrt (η / (1 - η)) * (2 * (1 + H) * τ8) + V / (1 - η))

lemma reciprocal_split {d Y0 Y : ℝ} (hd : 0 < d) (hY0 : 0 < Y0) (hY : d ≤ Y) :
    1 / Y ≤ 1 / Y0 + max 0 (Y0 - Y) / (d * Y0) := by
  have hy : 0 < Y := hd.trans_le hY
  by_cases h : Y0 ≤ Y
  · have hdiv := one_div_le_one_div_of_le hY0 h
    have hp : 0 ≤ max 0 (Y0 - Y) / (d * Y0) := by positivity
    linarith
  · have hdiff : 0 ≤ Y0 - Y := by linarith
    rw [max_eq_right hdiff]
    calc
      1 / Y = 1 / Y0 + (Y0 - Y) / (Y * Y0) := by field_simp; ring
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left hdiff (mul_pos hd hY0)
        (mul_le_mul_of_nonneg_right hY hY0.le))

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A deficit norm on the original measure gives an unnormalized kept reciprocal norm. -/
theorem reciprocal_on_kept {K : Set X} (hK : MeasurableSet K)
    (hmass : μ univ ≤ 1) {Y : X → ℝ} (mY : Measurable Y)
    {d Y0 D : ℝ} (hd : 0 < d) (hY0 : 0 < Y0)
    (hfloor : ∀ x ∈ K, d ≤ Y x)
    (hD : LBound μ 4 (fun x => max 0 (Y0 - Y x)) D) :
    LBound (μ.restrict K) 4 (fun x => 1 / Y x) (reciprocalBound d Y0 D) := by
  have hm : (μ.restrict K) univ ≤ 1 :=
    (Measure.restrict_le_self univ).trans hmass
  have hc := LBound.const (μ := μ.restrict K) (by norm_num : (4 : ℕ) ≠ 0) hm
    (show 0 ≤ 1 / Y0 by positivity)
  have hs := (hD.restrict K).scale (by norm_num : (4 : ℕ) ≠ 0)
    (show 0 ≤ (d * Y0)⁻¹ by positivity)
  have ha := hc.add (by norm_num) hs
  have hb : LBound (μ.restrict K) 4
      (fun x => 1 / Y0 + (d * Y0)⁻¹ * max 0 (Y0 - Y x))
      (reciprocalBound d Y0 D) := by
    simpa only [reciprocalBound, div_eq_mul_inv, mul_comm D, Nat.cast_ofNat] using ha
  apply hb.mono (measurable_const.div mY)
  apply (ae_restrict_iff' hK).mpr
  exact Filter.Eventually.of_forall fun x hx => by
    have hy : 0 < Y x := hd.trans_le (hfloor x hx)
    change |1 / Y x| ≤ |1 / Y0 + (d * Y0)⁻¹ * max 0 (Y0 - Y x)|
    rw [abs_of_pos (one_div_pos.mpr hy), abs_of_nonneg (by positivity)]
    simpa only [div_eq_mul_inv, mul_comm (max 0 (Y0 - Y x))] using
      reciprocal_split hd hY0 (hfloor x hx)

theorem SY {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y : X → ℝ} (mY : Measurable Y) {d Y0 H μ0 g8 : ℝ}
    (hd : 0 < d) (hY0 : d < Y0) (hfloor : ∀ x ∈ K, d ≤ Y x)
    (hdef : LBound μ 4 (fun x => max 0 (Y0 - Y x))
      (2 * H + g8 * (2 * μ0 + g8))) :
    LBound (μ.restrict K) 4 (fun x => 1 / Y x) (gammaY d Y0 H μ0 g8) :=
  reciprocal_on_kept hK hmass mY hd (hd.trans hY0) hfloor hdef

/-- SY holds at every real order between one and four. -/
theorem SY_orders {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y : X → ℝ} (mY : Measurable Y) {d Y0 H μ0 g8 : ℝ}
    (hd : 0 < d) (hY0 : d < Y0) (hfloor : ∀ x ∈ K, d ≤ Y x)
    (hdef : LBound μ 4 (fun x => max 0 (Y0 - Y x))
      (2 * H + g8 * (2 * μ0 + g8)))
    {q : ℝ≥0∞} (hq1 : 1 ≤ q) (hq4 : q ≤ 4) :
    LBound (μ.restrict K) q (fun x => 1 / Y x) (gammaY d Y0 H μ0 g8) := by
  apply (SY hK hmass mY hd hY0 hfloor hdef).lower
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)) (by norm_num) hq4
  exact (Measure.restrict_le_self univ).trans hmass

/-- The mixture scale receives mean-shift and conditional-variance prices. -/
theorem SY2 {K : Set X} (hK : MeasurableSet K) (hmass : μ univ ≤ 1)
    {Y Zg2 sd var : X → ℝ} (mZ : Measurable Zg2)
    {d Y0 H μ0 g8 η τ8 V : ℝ} (hd : 0 < d) (hY0 : d < Y0)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hfloor : ∀ x ∈ K, d ≤ Zg2 x)
    (hbase : LBound μ 4 (fun x => max 0 (Y0 - Y x))
      (2 * H + g8 * (2 * μ0 + g8)))
    (hsd : LBound μ 4 sd (2 * (1 + H) * τ8))
    (hvar : LBound μ 4 var V)
    (hloss : ∀ x, Y x - Zg2 x ≤ sqrt (η / (1 - η)) * |sd x| +
      |var x| / (1 - η)) :
    LBound (μ.restrict K) 4 (fun x => 1 / Zg2 x) (gMix d Y0 H μ0 g8 η τ8 V) := by
  have ha : LBound μ 4 (fun x => |sd x|) (2 * (1 + H) * τ8) :=
    hsd.mono hsd.measurable.abs (Filter.Eventually.of_forall fun x => by simp)
  have hb : LBound μ 4 (fun x => |var x|) V :=
    hvar.mono hvar.measurable.abs (Filter.Eventually.of_forall fun x => by simp)
  have hs := ha.scale (by norm_num : (4 : ℕ) ≠ 0) (sqrt_nonneg (η / (1 - η)))
  have hv := hb.scale (by norm_num : (4 : ℕ) ≠ 0)
    (show 0 ≤ (1 - η)⁻¹ by positivity)
  have hsum := (hbase.add (by norm_num) hs).add (by norm_num) hv
  have hsum' : LBound μ 4
      (fun x => max 0 (Y0 - Y x) + sqrt (η / (1 - η)) * |sd x| +
        (1 - η)⁻¹ * |var x|)
      (2 * H + g8 * (2 * μ0 + g8) + sqrt (η / (1 - η)) *
        (2 * (1 + H) * τ8) + V / (1 - η)) := by
    simpa only [div_eq_mul_inv, mul_comm V] using hsum
  have hdef : LBound μ 4 (fun x => max 0 (Y0 - Zg2 x))
      (2 * H + g8 * (2 * μ0 + g8) + sqrt (η / (1 - η)) *
        (2 * (1 + H) * τ8) + V / (1 - η)) := by
    apply hsum'.mono (g := fun x => max 0 (Y0 - Zg2 x))
      (measurable_const.max (measurable_const.sub mZ))
    apply Filter.Eventually.of_forall
    intro x
    rw [abs_of_nonneg (le_max_left _ _), abs_of_nonneg (by positivity)]
    apply max_le
    · positivity
    · have h := hloss x
      simp only [div_eq_mul_inv] at h ⊢
      have hm := le_max_right (0 : ℝ) (Y0 - Y x)
      nlinarith
  exact reciprocal_on_kept hK hmass mZ hd (hd.trans hY0) hfloor hdef

end BstLean.Part242
