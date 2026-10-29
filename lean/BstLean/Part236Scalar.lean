import BstLean.Part232Cells

/-! RF scalar prices and the complete radius/frame cover. -/
namespace BstLean.Part236
open Real

noncomputable def framePrice (q r S : ℝ) : ℝ :=
  if S ≤ r / (2 * q) then q * S ^ 2 else r * S - r ^ 2 / (4 * q)

lemma framePrice_le_split {q r x y : ℝ} (hq : 0 < q) (hy : 0 ≤ y) :
    framePrice q r (x + y) ≤ q * x ^ 2 + r * y := by
  unfold framePrice
  split_ifs with h
  · have ht' : (x + y) * (2 * q) ≤ r := (le_div_iff₀ (by positivity : 0 < 2 * q)).mp h
    have ht : 2 * q * (x + y) ≤ r := by nlinarith only [ht']
    nlinarith [mul_nonneg hy (show 0 ≤ r - 2 * q * (x + y) by linarith),
      mul_nonneg hq.le (sq_nonneg y)]
  · have he : (r / (2 * q)) ^ 2 * q = r ^ 2 / (4 * q) := by field_simp; ring
    have ht := mul_nonneg hq.le (sq_nonneg (x - r / (2 * q)))
    have hd : 2 * q * (r / (2 * q)) = r := by field_simp
    have hEq : q * x ^ 2 + r * y - (r * (x + y) - r ^ 2 / (4 * q)) =
        q * (x - r / (2 * q)) ^ 2 := by
      field_simp
      <;> ring
    linarith only [ht, hEq]

lemma framePrice_mono {q r a b : ℝ} (hq : 0 < q) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hab : a ≤ b) : framePrice q r a ≤ framePrice q r b := by
  unfold framePrice
  split_ifs with hA hB hB
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) hq.le
  · have hc : r / (2 * q) ≤ b := le_of_not_ge hB
    have he : q * (r / (2 * q)) ^ 2 = r * (r / (2 * q)) - r ^ 2 / (4 * q) := by field_simp; ring
    have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hA 2) hq.le
    have hl := mul_le_mul_of_nonneg_left hc hr
    linarith
  · exact False.elim (hA (hab.trans hB))
  · exact sub_le_sub_right (mul_le_mul_of_nonneg_left hab hr) _

lemma framePrice_nonneg {q r S : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (hS : 0 ≤ S) :
    0 ≤ framePrice q r S := by
  have h := framePrice_mono hq hr (le_refl (0 : ℝ)) hS
  simpa [framePrice, show (0 : ℝ) ≤ r / (2 * q) by positivity] using h

structure FrameCover extends BstLean.Part232.RadiusCover where
  maximum : ℝ
  last : h K = maximum

theorem product_majorant (R : BstLean.Part232.RadiusCover) (C : FrameCover)
    {q r c₀ c₁ x y ρ F : ℝ} {g : ℕ → ℕ → ℝ}
    (hq : 0 < q) (hr : 0 ≤ r) (hc₁ : 0 ≤ c₁)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hρ : 0 ≤ ρ) (hmax : x + y ≤ C.maximum)
    (hline : ∀ i < R.K, ∀ j < C.K,
      g i j ≤ c₀ + c₁ * R.h i ^ 2 + framePrice q r (C.h j))
    (hterminal : 1 ≤ c₀ + c₁ * R.h R.K ^ 2)
    (hfinite : ∀ i < R.K, ∀ j < C.K,
      BstLean.Part232.radiusCell R.h i ρ →
      BstLean.Part232.radiusCell C.h j (x + y) → F ≤ g i j)
    (htail : R.h R.K < ρ → F ≤ 1) :
    F ≤ c₀ + c₁ * ρ ^ 2 + q * x ^ 2 + r * y := by
  rcases BstLean.Part232.radius_cover C.positive (add_nonneg hx hy) with
    ⟨j, hj, hcell⟩ | hlast
  · have hS : C.h j ≤ x + y := by
      by_cases hz : j = 0
      · subst j; rw [C.zero]; exact add_nonneg hx hy
      · exact (by simpa [BstLean.Part232.radiusCell, hz] using hcell.1 : C.h j < x + y).le
    have hm := (framePrice_mono hq hr (C.toRadiusCover.nonneg (by omega)) hS).trans
      (framePrice_le_split hq hy)
    rcases BstLean.Part232.radius_cover R.positive hρ with ⟨i, hi, hc⟩ | ht
    · have hb := hfinite i hi j hj hc hcell
      have hl := hline i hi j hj
      have hp := mul_le_mul_of_nonneg_left (R.lower_square hi hρ hc) hc₁
      linarith
    · have hp := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (R.nonneg le_rfl) ht.le 2) hc₁
      have hn := add_nonneg (mul_nonneg hq.le (sq_nonneg x)) (mul_nonneg hr hy)
      linarith [htail ht]
  · rw [C.last] at hlast
    linarith
end BstLean.Part236
