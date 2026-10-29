import BstLean.Part245Analytic

namespace BstLean.Part245
open Real BstLean.Part130 BstLean.Part182

theorem badd {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (hl : l ≤ a + c) (hu : b + d ≤ u) :
    l ≤ x + y ∧ x + y ≤ u := ⟨hl.trans (add_le_add hx.1 hy.1),
      (add_le_add hx.2 hy.2).trans hu⟩

theorem bsub {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (hl : l ≤ a - d) (hu : b - c ≤ u) :
    l ≤ x - y ∧ x - y ≤ u := ⟨hl.trans (sub_le_sub hx.1 hy.2),
      (sub_le_sub hx.2 hy.1).trans hu⟩

theorem bmul {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hl : l ≤ a * c) (hu : b * d ≤ u) : l ≤ x * y ∧ x * y ≤ u :=
  ⟨hl.trans (mul_le_mul hx.1 hy.1 hc (ha.trans hx.1)),
    (mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))).trans hu⟩

theorem bdiv {x y a b c d l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 < c)
    (hl : l ≤ a / d) (hu : b / c ≤ u) : l ≤ x / y ∧ x / y ≤ u := by
  have h := BstLean.Part193.Interval.div_nonneg_bounds hx hy ha hc
  exact ⟨hl.trans h.1, h.2.trans hu⟩

theorem bsqrt {x a b l u : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u) (hl : l ^ 2 ≤ a) (hu : b ≤ u ^ 2) :
    l ≤ √x ∧ √x ≤ u :=
  BstLean.Part193.Interval.sqrt_bounds hl0 hu0 (hl.trans hx.1) (hx.2.trans hu)

theorem bsq {x a b l u : ℝ} (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a)
    (hl : l ≤ a ^ 2) (hu : b ^ 2 ≤ u) : l ≤ x ^ 2 ∧ x ^ 2 ≤ u :=
  ⟨hl.trans (pow_le_pow_left₀ ha hx.1 2),
    (pow_le_pow_left₀ (ha.trans hx.1) hx.2 2).trans hu⟩

theorem kappa_073_bounds : (7726 / 10000 : ℝ) ≤ kappa (73 / 100) ∧
    kappa (73 / 100) ≤ 774 / 1000 := by
  have hs : (6834 / 10000 : ℝ) ≤ √(1 - (73 / 100 : ℝ) ^ 2) ∧
      √(1 - (73 / 100 : ℝ) ^ 2) ≤ 6835 / 10000 := by
    apply BstLean.Part193.Interval.sqrt_bounds <;> norm_num
  have hpi := sn_pi_hi
  have hk := kdot_073_lower
  have hid : kappa (73 / 100) = √(1 - (73 / 100 : ℝ) ^ 2) / π +
      (73 / 100) * kdot (73 / 100) := by unfold kappa kdot; field_simp
  constructor
  · rw [hid]
    have hd : (6834 / 10000 : ℝ) / (3141593 / 1000000) ≤
        √(1 - (73 / 100 : ℝ) ^ 2) / π :=
      (div_le_div_of_nonneg_right hs.1 (by norm_num)).trans
        (div_le_div_of_nonneg_left (by positivity) Real.pi_pos hpi.le)
    linarith
  · exact (sn_kappa_le (by norm_num) (by norm_num) hs.2).trans (by norm_num)

end BstLean.Part245
