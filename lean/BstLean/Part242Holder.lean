import BstLean.Part242Norm

/-! The SY exponent allocation uses reciprocal order four. -/
namespace BstLean.Part242
open MeasureTheory Real
open scoped ENNReal

instance holder8_4 : ENNReal.HolderTriple (8 : ℝ≥0∞) 4 (8 / 3) := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder8_83 : ENNReal.HolderTriple (8 : ℝ≥0∞) (8 / 3) 2 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder8_8 : ENNReal.HolderTriple (8 : ℝ≥0∞) 8 4 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder4_4 : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder12_4 : ENNReal.HolderTriple (12 : ℝ≥0∞) 4 3 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder24_8 : ENNReal.HolderTriple (24 : ℝ≥0∞) 8 6 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

instance holder4_43 : ENNReal.HolderTriple (4 : ℝ≥0∞) (4 / 3) 1 := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (by norm_num) (by norm_num)).mp
  norm_num [ENNReal.toReal_add]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma eighthirds_ne_top : (8 / 3 : ℝ≥0∞) ≠ ∞ :=
  ENNReal.div_ne_top (by norm_num) (by norm_num)

lemma two_le_eighthirds : (2 : ℝ≥0∞) ≤ 8 / 3 := by
  apply (ENNReal.toReal_le_toReal (by norm_num) eighthirds_ne_top).mp
  norm_num [ENNReal.toReal_div]

lemma fourthirds_ne_zero : (4 / 3 : ℝ≥0∞) ≠ 0 :=
  ENNReal.div_ne_zero.mpr ⟨by norm_num, by norm_num⟩

lemma fourthirds_le_four : (4 / 3 : ℝ≥0∞) ≤ 4 := by
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (by norm_num)).mp
  norm_num [ENNReal.toReal_div]

theorem SY_location_div {df R : X → ℝ} {af Γ : ℝ}
    (hd : LBound μ 8 df af) (hR : LBound μ 4 R Γ) :
    LBound μ (8 / 3) (fun x => df x * R x) (af * Γ) := hd.mul hR

theorem SY_location_product {f df R : X → ℝ} {F af Γ : ℝ}
    (hf : LBound μ 8 f F) (hd : LBound μ 8 df af) (hR : LBound μ 4 R Γ) :
    LBound μ 2 (fun x => f x * (df x * R x)) (F * (af * Γ)) :=
  hf.mul (SY_location_div hd hR)

theorem SY_exceptional_product {f df : X → ℝ} {F af : ℝ}
    (hf : LBound μ 24 f F) (hd : LBound μ 8 df af) :
    LBound μ 6 (fun x => f x * df x) (F * af) := hf.mul hd

/-- The integrated mixture terms use orders four/four and twelve/four. -/
theorem SY2_products {v R : X → ℝ} {V Γ : ℝ}
    (hv4 : LBound μ 4 v V) (hv12 : LBound μ 12 v V) (hR : LBound μ 4 R Γ) :
    LBound μ 2 (fun x => v x * R x) (V * Γ) ∧
      LBound μ 3 (fun x => v x * R x) (V * Γ) := ⟨hv4.mul hR, hv12.mul hR⟩

end BstLean.Part242
