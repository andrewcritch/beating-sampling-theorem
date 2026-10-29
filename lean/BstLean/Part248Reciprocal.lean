import BstLean.Part242Reciprocal

/-! Finite reciprocal expansions on the original retained distribution. -/
namespace BstLean.Part248
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part242

noncomputable def expansion (k : ℕ) (d Y0 D : ℝ) : ℝ :=
  (∑ j ∈ Finset.range k, D ^ j / Y0 ^ (j + 1)) + D ^ k / (d * Y0 ^ k)

lemma expansion_zero (d Y0 D : ℝ) : expansion 0 d Y0 D = 1 / d := by
  simp [expansion]

lemma expansion_succ (k : ℕ) {d Y0 D : ℝ} (hd : d ≠ 0) (hY0 : Y0 ≠ 0) :
    expansion (k + 1) d Y0 D = 1 / Y0 + D / Y0 * expansion k d Y0 D := by
  unfold expansion
  rw [Finset.sum_range_succ']
  have hs : (∑ j ∈ Finset.range k, D ^ (j + 1) / Y0 ^ (j + 1 + 1)) =
      D / Y0 * ∑ j ∈ Finset.range k, D ^ j / Y0 ^ (j + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pow_succ]
    field_simp
  rw [hs]
  simp only [pow_zero, pow_one, pow_succ]
  field_simp
  <;> ring

/-- R holds at every finite expansion order. -/
theorem R (k : ℕ) {d Y0 Y : ℝ} (hd : 0 < d) (hY0 : 0 < Y0) (hY : d ≤ Y) :
    1 / Y ≤ expansion k d Y0 (max 0 (Y0 - Y)) := by
  have hy : 0 < Y := hd.trans_le hY
  have hD : 0 ≤ max 0 (Y0 - Y) := le_max_left _ _
  have hstep : 1 / Y ≤ 1 / Y0 + max 0 (Y0 - Y) / Y0 * (1 / Y) := by
    have hm := le_max_right (0 : ℝ) (Y0 - Y)
    apply (div_le_iff₀ hy).mpr
    field_simp
    nlinarith
  induction k with
  | zero => simpa [expansion_zero] using one_div_le_one_div_of_le hd hY
  | succ k ih =>
    rw [expansion_succ k hd.ne' hY0.ne']
    exact hstep.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left ih (div_nonneg hD hY0.le)))

#print axioms R
end BstLean.Part248
