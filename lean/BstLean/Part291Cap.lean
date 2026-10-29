import BstLean.Part229Split

/-! Pointwise factors F4 and F6 for the actual capped derivative. -/
namespace BstLean.BlueprintLow
open Real MeasureTheory
open BstLean.Part130 BstLean.Part188 BstLean.Part229

theorem capSlope_sq_active {a d f : ℝ} (hd : 0 < d) (ha : d < a - f ^ 2) :
    capSlope a d f ^ 2 = (f ^ 2 / (a - f ^ 2) ^ 2) * weightSq a d f := by
  have hp : 0 < a - f ^ 2 := hd.trans ha
  simp only [capSlope, if_pos ha, div_pow, mul_pow, sq_sqrt hp.le,
    weightSq, max_eq_left ha.le]
  field_simp

theorem capSlope_sq_weight {a d f : ℝ} (hd : 0 < d) (had : d ≤ a) :
    capSlope a d f ^ 2 ≤ (a - d) / d ^ 2 * weightSq a d f := by
  by_cases h : d < a - f ^ 2
  · rw [capSlope_sq_active hd h]
    apply mul_le_mul_of_nonneg_right _ (weightSq_nonneg hd)
    have hf : f ^ 2 ≤ a - d := by linarith
    exact div_le_div₀ (by linarith) hf (sq_pos_of_pos hd)
      (pow_le_pow_left₀ hd.le h.le 2)
  · simp only [capSlope, if_neg h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr had) (sq_nonneg _)) (weightSq_nonneg hd)

theorem capSlope_sq_bound {a d f : ℝ} (hd : 0 < d) (had : d ≤ a) :
    capSlope a d f ^ 2 ≤ (a - d) / d ^ 3 := by
  calc
    _ ≤ (a - d) / d ^ 2 * weightSq a d f := capSlope_sq_weight hd had
    _ ≤ (a - d) / d ^ 2 * (1 / d) := mul_le_mul_of_nonneg_left
      (weightSq_le_inv hd) (div_nonneg (sub_nonneg.mpr had) (sq_nonneg _))
    _ = _ := by ring

theorem capEnergy_pointwise {n : ℕ} (f z : (Fin n → ℝ) → ℝ)
    {a d : ℝ} (hd : 0 < d) (had : d ≤ a) (ξ : Fin n → ℝ) :
    capEnergy a d f z ξ ≤
      (weightSq a d (f ξ) * z ξ ^ 2) *
        ((a - d) / d ^ 2 * BstLean.Part151.gradSq f ξ) := by
  rw [(energy_formulas a d f z ξ).2, mul_pow]
  have hg : normSq (gradientVector f ξ) = BstLean.Part151.gradSq f ξ := rfl
  rw [hg]
  have h := mul_le_mul_of_nonneg_left (capSlope_sq_weight (f := f ξ) hd had) (sq_nonneg (z ξ))
  have h' := mul_le_mul_of_nonneg_right h
    (show 0 ≤ BstLean.Part151.gradSq f ξ from normSq_nonneg (gradientVector f ξ))
  convert h' using 1 <;> ring

end BstLean.BlueprintLow
