import BstLean.Part197Bounds
import BstLean.Part246TI
import BstLean.Part245Analytic

/-! Rational interval rules for the local TI certificates. -/
namespace BstLean.Part255
open Real BstLean.Part130 BstLean.Part182 BstLean.Part197

def B (l u x : ℝ) : Prop := l ≤ x ∧ x ≤ u

theorem bpoint (x : ℝ) : B x x x := ⟨le_rfl, le_rfl⟩

theorem bweaken {a b l u x : ℝ} (h : B a b x) (hl : l ≤ a) (hu : b ≤ u) :
    B l u x := ⟨hl.trans h.1, h.2.trans hu⟩

theorem badd {a b c d l u x y : ℝ} (hx : B a b x) (hy : B c d y)
    (hl : l ≤ a + c) (hu : b + d ≤ u) : B l u (x + y) :=
  ⟨hl.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hu⟩

theorem bsub {a b c d l u x y : ℝ} (hx : B a b x) (hy : B c d y)
    (hl : l ≤ a - d) (hu : b - c ≤ u) : B l u (x - y) :=
  ⟨hl.trans (sub_le_sub hx.1 hy.2), (sub_le_sub hx.2 hy.1).trans hu⟩

theorem bmul {a b c d l u x y : ℝ} (hx : B a b x) (hy : B c d y)
    (hl : l ≤ min (min (a*c) (a*d)) (min (b*c) (b*d)))
    (hu : max (max (a*c) (a*d)) (max (b*c) (b*d)) ≤ u) : B l u (x*y) := by
  have h := BstLean.Part193.Interval.mem_mul
    (I := ⟨a,b,hx.1.trans hx.2⟩) (J := ⟨c,d,hy.1.trans hy.2⟩) hx hy
  exact ⟨hl.trans h.1, h.2.trans hu⟩

theorem bdiv {a b c d l u x y : ℝ} (hx : B a b x) (hy : B c d y)
    (hc : 0 < c)
    (hl : l ≤ min (min (a/d) (a/c)) (min (b/d) (b/c)))
    (hu : max (max (a/d) (a/c)) (max (b/d) (b/c)) ≤ u) : B l u (x/y) := by
  have h := BstLean.Part193.Interval.mem_divPos
    (I := ⟨a,b,hx.1.trans hx.2⟩) (J := ⟨c,d,hy.1.trans hy.2⟩) hx hy hc
  constructor
  · apply hl.trans
    simpa only [BstLean.Part193.Interval.divPos, BstLean.Part193.Interval.mul,
      BstLean.Part193.Interval.invPos, div_eq_mul_inv, one_mul] using h.1
  · apply le_trans _ hu
    simpa only [BstLean.Part193.Interval.divPos, BstLean.Part193.Interval.mul,
      BstLean.Part193.Interval.invPos, div_eq_mul_inv, one_mul] using h.2

theorem bsqrt {a b l u x : ℝ} (h : B a b x)
    (hl0 : 0 ≤ l) (hu0 : 0 ≤ u) (hl : l^2 ≤ a) (hu : b ≤ u^2) :
    B l u (√x) :=
  BstLean.Part193.Interval.sqrt_bounds hl0 hu0 (hl.trans h.1) (h.2.trans hu)

theorem bsq {a b l u x : ℝ} (h : B a b x) (ha : 0 ≤ a)
    (hl : l ≤ a^2) (hu : b^2 ≤ u) : B l u (x^2) :=
  ⟨hl.trans (pow_le_pow_left₀ ha h.1 2),
    (pow_le_pow_left₀ (ha.trans h.1) h.2 2).trans hu⟩

theorem bkdot_upper {c q a d : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hq : 0 ≤ q) (hqs : q^2 ≤ (1-c)/(1+c))
    (ha : a ≤ atanSum 24 q - q^49/49) (ha0 : 0 ≤ a)
    (hd : 1 - 2*a/(314159265358979323847 / 10^20) ≤ d) : kdot c ≤ d := by
  have hr : q ≤ angleRatio c := Real.le_sqrt_of_sq_le hqs
  have ht := (abs_le.mp (atan_remainder hq 24)).1
  have hat : a ≤ Real.arctan q := by norm_num at ht; linarith
  have hac : 2*a ≤ Real.arccos c := by
    rw [arccos_half_angle hc hc1]
    linarith [Real.arctan_mono hr]
  have hdiv : 2*a/(314159265358979323847 / 10^20) ≤ Real.arccos c / π :=
    (div_le_div_of_nonneg_left (by positivity) Real.pi_pos pi_mem.2).trans
      (div_le_div_of_nonneg_right hac Real.pi_pos.le)
  unfold kdot
  linarith

theorem bkdot_lower {c q a d : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hq : 0 ≤ q) (hqs : (1-c)/(1+c) ≤ q^2)
    (ha : atanSum 24 q + q^49/49 ≤ a) (ha0 : 0 ≤ a)
    (hd : d ≤ 1 - 2*a/(314159265358979323846 / 10^20)) : d ≤ kdot c := by
  have hr : angleRatio c ≤ q := (Real.sqrt_le_left hq).2 hqs
  have ht := (abs_le.mp (atan_remainder hq 24)).2
  have hat : Real.arctan q ≤ a := by norm_num at ht; linarith
  have hac : Real.arccos c ≤ 2*a := by
    rw [arccos_half_angle hc hc1]
    linarith [Real.arctan_mono hr]
  have hdiv : Real.arccos c / π ≤ 2*a/(314159265358979323846 / 10^20) :=
    (div_le_div_of_nonneg_right hac Real.pi_pos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by norm_num) pi_mem.1)
  unfold kdot
  linarith

theorem bkdot {a b l u x : ℝ} (hx : B a b x)
    (hl : l ≤ kdot a) (hu : kdot b ≤ u) : B l u (kdot x) :=
  ⟨hl.trans (BstLean.Part245.kdot_mono hx.1),
    (BstLean.Part245.kdot_mono hx.2).trans hu⟩

theorem bkappa {a b l u x : ℝ} (hx : B a b x) (ha : -1 ≤ a) (hb : b ≤ 1)
    (hl : l ≤ kappa a) (hu : kappa b ≤ u) : B l u (kappa x) := by
  have hab := hx.1.trans hx.2
  exact ⟨hl.trans (kappa_monotoneOn ⟨ha,hab.trans hb⟩ ⟨ha.trans hx.1,hx.2.trans hb⟩ hx.1),
    (kappa_monotoneOn ⟨ha.trans hx.1,hx.2.trans hb⟩ ⟨ha.trans hab,hb⟩ hx.2).trans hu⟩

theorem kappa_eq (c : ℝ) : kappa c = √(1-c^2)/π + c*kdot c := by
  unfold kappa kdot
  field_simp

theorem bfirst {a b c d x y : ℝ} (hx : B a b x) (hy : B c d y)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    B (min (min (c*a) (d*a)) (a/2))
      (if 0 ≤ b then d*b else b/2) (if 0 ≤ x then y*x else x/2) := by
  constructor
  · split_ifs with h
    · have h1 : min (c*a) (d*a) ≤ y*a := by
        by_cases ha : 0 ≤ a
        · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hy.1 ha)
        · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hy.2 (le_of_not_ge ha))
      exact (min_le_left _ _).trans (h1.trans (mul_le_mul_of_nonneg_left hx.1 (hc.trans hy.1)))
    · exact (min_le_right _ _).trans (div_le_div_of_nonneg_right hx.1 (by norm_num))
  · by_cases hb : 0 ≤ b
    · rw [if_pos hb]
      split_ifs with h
      · exact mul_le_mul hy.2 hx.2 h hd
      · have : x / 2 ≤ 0 := by linarith
        exact this.trans (mul_nonneg hd hb)
    · rw [if_neg hb, if_neg (fun h => hb (h.trans hx.2))]
      exact div_le_div_of_nonneg_right hx.2 (by norm_num)

theorem bmin {a b c d x y : ℝ} (hx : B a b x) (hy : B c d y) :
    B (min a c) (min b d) (min x y) :=
  ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩

theorem bmax {a b c d x y : ℝ} (hx : B a b x) (hy : B c d y) :
    B (max a c) (max b d) (max x y) :=
  ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩

theorem babs {a b x : ℝ} (hx : B a b x) : B 0 (max (-a) b) |x| := by
  refine ⟨abs_nonneg _, abs_le.mpr ⟨?_, ?_⟩⟩
  · have := le_max_left (-a) b
    linarith [hx.1]
  · exact hx.2.trans (le_max_right _ _)

end BstLean.Part255
