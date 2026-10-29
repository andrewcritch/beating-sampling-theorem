import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Part 193: closed real interval rules for scalar certificates.
All endpoints are exact real numbers. Rational endpoints embed into these rules.
Positive division includes a checked lower denominator bound. -/
namespace BstLean.Part193

/-- A closed interval with a checked endpoint order. -/
structure Interval where
  lo : ℝ
  hi : ℝ
  ordered : lo ≤ hi

namespace Interval

def Mem (I : Interval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

noncomputable def point (x : ℝ) : Interval := ⟨x, x, le_rfl⟩
noncomputable def add (I J : Interval) : Interval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.ordered J.ordered⟩
noncomputable def neg (I : Interval) : Interval :=
  ⟨-I.hi, -I.lo, neg_le_neg I.ordered⟩
noncomputable def sub (I J : Interval) : Interval := add I (neg J)
noncomputable def maxInterval (I J : Interval) : Interval :=
  ⟨max I.lo J.lo, max I.hi J.hi, max_le_max I.ordered J.ordered⟩
noncomputable def minInterval (I J : Interval) : Interval :=
  ⟨min I.lo J.lo, min I.hi J.hi, min_le_min I.ordered J.ordered⟩
noncomputable def hull (I J : Interval) : Interval :=
  ⟨min I.lo J.lo, max I.hi J.hi,
    (min_le_left _ _).trans (I.ordered.trans (le_max_left _ _))⟩

@[simp] theorem mem_point (x : ℝ) : (point x).Mem x := ⟨le_rfl, le_rfl⟩
theorem mem_add {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (add I J).Mem (x + y) := ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩
theorem mem_neg {I : Interval} {x : ℝ} (hx : I.Mem x) :
    (neg I).Mem (-x) := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩
theorem mem_sub {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (sub I J).Mem (x - y) := by simpa [sub, sub_eq_add_neg] using mem_add hx (mem_neg hy)
theorem mem_max {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (maxInterval I J).Mem (max x y) := ⟨max_le_max hx.1 hy.1, max_le_max hx.2 hy.2⟩
theorem mem_min {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (minInterval I J).Mem (min x y) := ⟨min_le_min hx.1 hy.1, min_le_min hx.2 hy.2⟩
theorem mem_hull_left {I J : Interval} {x : ℝ} (hx : I.Mem x) :
    (hull I J).Mem x :=
  ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩
theorem mem_hull_right {I J : Interval} {x : ℝ} (hx : J.Mem x) :
    (hull I J).Mem x :=
  ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩
theorem mem_weaken {I J : Interval} {x : ℝ} (hx : I.Mem x)
    (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) : J.Mem x :=
  ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Four corner products bound multiplication without sign assumptions. -/
noncomputable def mul (I J : Interval) : Interval where
  lo := min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi))
  hi := max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))
  ordered := (min_le_left _ _).trans ((min_le_left _ _).trans
    ((le_max_left _ _).trans (le_max_left _ _)))

private theorem linear_bounds {a b x c L U : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (ha : L ≤ a * c ∧ a * c ≤ U) (hb : L ≤ b * c ∧ b * c ≤ U) :
    L ≤ x * c ∧ x * c ≤ U := by
  by_cases hc : 0 ≤ c
  · exact ⟨ha.1.trans (mul_le_mul_of_nonneg_right hx.1 hc),
      (mul_le_mul_of_nonneg_right hx.2 hc).trans hb.2⟩
  · have hc' : c ≤ 0 := le_of_lt (lt_of_not_ge hc)
    exact ⟨hb.1.trans (mul_le_mul_of_nonpos_right hx.2 hc'),
      (mul_le_mul_of_nonpos_right hx.1 hc').trans ha.2⟩

theorem mem_mul {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (mul I J).Mem (x * y) := by
  have hll : (mul I J).Mem (I.lo * J.lo) :=
    ⟨(min_le_left _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_left _ _)⟩
  have hlh : (mul I J).Mem (I.lo * J.hi) :=
    ⟨(min_le_left _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_left _ _)⟩
  have hhl : (mul I J).Mem (I.hi * J.lo) :=
    ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩
  have hhh : (mul I J).Mem (I.hi * J.hi) :=
    ⟨(min_le_right _ _).trans (min_le_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hl := linear_bounds (c := I.lo) (L := (mul I J).lo) (U := (mul I J).hi)
    hy (by simpa only [Mem, mul_comm] using hll)
    (by simpa only [Mem, mul_comm] using hlh)
  have hh := linear_bounds (c := I.hi) (L := (mul I J).lo) (U := (mul I J).hi)
    hy (by simpa only [Mem, mul_comm] using hhl)
    (by simpa only [Mem, mul_comm] using hhh)
  exact linear_bounds hx (by simpa [mul_comm] using hl) (by simpa [mul_comm] using hh)

noncomputable def invPos (I : Interval) (h : 0 < I.lo) : Interval :=
  ⟨1 / I.hi, 1 / I.lo, div_le_div_of_nonneg_left (by norm_num) h I.ordered⟩

theorem mem_invPos {I : Interval} {x : ℝ} (hx : I.Mem x) (h : 0 < I.lo) :
    (invPos I h).Mem (1 / x) := by
  have hx0 : 0 < x := h.trans_le hx.1
  exact ⟨div_le_div_of_nonneg_left (by norm_num) hx0 hx.2,
    div_le_div_of_nonneg_left (by norm_num) h hx.1⟩

/-- A positive denominator suffices; the numerator can have either sign. -/
noncomputable def divPos (I J : Interval) (h : 0 < J.lo) : Interval :=
  mul I (invPos J h)

theorem mem_divPos {I J : Interval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y)
    (h : 0 < J.lo) : (divPos I J h).Mem (x / y) := by
  simpa [divPos, div_eq_mul_inv] using mem_mul hx (mem_invPos hy h)

/-- The sharp positive-division rule for a nonnegative numerator. -/
theorem div_nonneg_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) (ha : 0 ≤ a) (hc : 0 < c) :
    a / d ≤ x / y ∧ x / y ≤ b / c := by
  exact ⟨div_le_div₀ (ha.trans hx.1) hx.1 (hc.trans_le hy.1) hy.2,
    div_le_div₀ ((ha.trans hx.1).trans hx.2) hx.2 hc hy.1⟩

noncomputable def sqrt (I : Interval) : Interval :=
  ⟨Real.sqrt I.lo, Real.sqrt I.hi, Real.sqrt_le_sqrt I.ordered⟩
theorem mem_sqrt {I : Interval} {x : ℝ} (hx : I.Mem x) :
    (sqrt I).Mem (Real.sqrt x) :=
  ⟨Real.sqrt_le_sqrt hx.1, Real.sqrt_le_sqrt hx.2⟩

/-- Squared rational endpoints can certify a root without computing the root. -/
theorem sqrt_bounds {a b x : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : a ^ 2 ≤ x) (hu : x ≤ b ^ 2) : a ≤ Real.sqrt x ∧ Real.sqrt x ≤ b :=
  ⟨Real.le_sqrt_of_sq_le hl, (Real.sqrt_le_left hb).2 hu⟩

/-- Repeated interval multiplication works for every real base. -/
noncomputable def pow (I : Interval) : ℕ → Interval
  | 0 => point 1
  | k+1 => mul (pow I k) I

theorem mem_pow {I : Interval} {x : ℝ} (hx : I.Mem x) (k : ℕ) :
    (pow I k).Mem (x ^ k) := by
  induction k with
  | zero => simp [pow, point, Mem]
  | succ k ih => simpa [pow, pow_succ] using mem_mul ih hx

/-- Endpoint powers give a tighter rule on a nonnegative interval. -/
theorem pow_nonneg_bounds {a b x : ℝ} (hx : a ≤ x ∧ x ≤ b) (ha : 0 ≤ a)
    (k : ℕ) : a ^ k ≤ x ^ k ∧ x ^ k ≤ b ^ k :=
  ⟨pow_le_pow_left₀ ha hx.1 k, pow_le_pow_left₀ (ha.trans hx.1) hx.2 k⟩

/-- Negative integer powers use the positive reciprocal interval. -/
noncomputable def powNonneg (I : Interval) (h : 0 ≤ I.lo) (k : ℕ) : Interval :=
  ⟨I.lo ^ k, I.hi ^ k, pow_le_pow_left₀ h I.ordered k⟩

theorem mem_powNonneg {I : Interval} {x : ℝ} (hx : I.Mem x) (h : 0 ≤ I.lo)
    (k : ℕ) : (powNonneg I h k).Mem (x ^ k) := pow_nonneg_bounds hx h k

noncomputable def zpowPos (I : Interval) (h : 0 < I.lo) : ℤ → Interval
  | .ofNat k => powNonneg I h.le k
  | .negSucc k => invPos (powNonneg I h.le (k+1)) (pow_pos h (k+1))

theorem mem_zpowPos {I : Interval} {x : ℝ} (hx : I.Mem x) (h : 0 < I.lo)
    (k : ℤ) : (zpowPos I h k).Mem (x ^ k) := by
  cases k with
  | ofNat k => simpa [zpowPos] using mem_powNonneg hx h.le k
  | negSucc k =>
    simpa [zpowPos, zpow_negSucc, one_div] using
      (mem_invPos (mem_powNonneg hx h.le (k + 1)) (pow_pos h (k + 1)))

noncomputable def sum {ι : Type*} (s : Finset ι) (I : ι → Interval) : Interval :=
  ⟨∑ i ∈ s, (I i).lo, ∑ i ∈ s, (I i).hi,
    Finset.sum_le_sum fun i _ => (I i).ordered⟩

theorem mem_sum {ι : Type*} {s : Finset ι} {I : ι → Interval} {x : ι → ℝ}
    (hx : ∀ i ∈ s, (I i).Mem (x i)) : (sum s I).Mem (∑ i ∈ s, x i) :=
  ⟨Finset.sum_le_sum fun i hi => (hx i hi).1,
    Finset.sum_le_sum fun i hi => (hx i hi).2⟩

/-- A branch with a proved condition can retain its own interval. -/
theorem mem_ite {P : Prop} [Decidable P] {I J : Interval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : (if P then I else J).Mem (if P then x else y) := by
  split <;> assumption

/-- An unresolved branch uses the hull, including a cell that crosses zero. -/
theorem mem_ite_hull {P : Prop} [Decidable P] {I J : Interval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) : (hull I J).Mem (if P then x else y) := by
  split
  · exact mem_hull_left hx
  · exact mem_hull_right hy

theorem max_eq_left_of_separated {I J : Interval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) (h : J.hi ≤ I.lo) : max x y = x :=
  max_eq_left (hy.2.trans (h.trans hx.1))
theorem min_eq_right_of_separated {I J : Interval} {x y : ℝ}
    (hx : I.Mem x) (hy : J.Mem y) (h : J.hi ≤ I.lo) : min x y = y :=
  min_eq_right (hy.2.trans (h.trans hx.1))

end Interval
end BstLean.Part193
