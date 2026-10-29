import BstLean.Part159Q1

/-!
# Part 159 (file `Asin`): the partial sums of the inverse sine series

Role: `delegations/statements/p159-spec.md`, item 3 (toward `ConstK`). Do not use `sorry`,
`native_decide` or `axiom`.

Paper: `theorem7-01-statement-program.tex`, step 1: `Q_T(v) = Σ_{j<T} (2j)! v^{2j+1}/(4^j (j!)²
(2j+1))` (`QTsum` of Part 157).

`b_j = (2j)!/(4^j (j!)²)`, `P_T(x) = Σ_{j<T} b_j x^j` (the partial sum of the series of
`(1 − x)^{−1/2}`).

* `PT_tel`: `−P_T + 2(1 − x)P_T′ = −2T·b_T·x^{T−1}`.
* `PT_bounds`: for `T ≥ 1`, `0 ≤ x < 1`:
  `1/√(1 − x) − b_T·x^T/(1 − x) ≤ P_T(x) ≤ 1/√(1 − x)` (no infinite series: the function
  `√(1 − x)·P_T(x)` is monotone).
* **`QTsum_err`**: for `T ≥ 1`, `0 ≤ v < 1`: `0 ≤ arcsin v − Q_T(v) ≤ v·(v²)^T/(1 − v²)`.
-/

namespace BstLean.Part159

open Real Set
open BstLean.Part157 (QTsum)

/-- From a nonnegative derivative on `[a, b]` to `f a ≤ f b`. -/
lemma le_of_hasDeriv_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f' x) : f a ≤ f b := by
  have hmono : MonotoneOn f (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hd x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hd x (Ioo_subset_Icc_self hx)).deriv]
      exact hnn x hx
  exact hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab

/-- `b_j = (2j)!/(4^j (j!)²)`. -/
noncomputable def bB (j : ℕ) : ℝ := ((2 * j).factorial : ℝ) / (4 ^ j * (j.factorial : ℝ) ^ 2)

lemma bB_zero : bB 0 = 1 := by simp [bB]

lemma bB_pos (j : ℕ) : 0 < bB j := by unfold bB; positivity

lemma bB_succ (j : ℕ) : bB (j + 1) = bB j * ((2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2)) := by
  unfold bB
  have e1 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
  rw [e1, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  have h1 : ((2 * j).factorial : ℝ) ≠ 0 := by positivity
  have h2 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h3 : (2 * (j : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma bB_le_one (j : ℕ) : bB j ≤ 1 := by
  induction j with
  | zero => rw [bB_zero]
  | succ j ih =>
    rw [bB_succ]
    have h1 : (2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : 0 ≤ (2 * (j : ℝ) + 1) / (2 * (j : ℝ) + 2) := by positivity
    nlinarith [bB_pos j]

/-- `P_T(x) = Σ_{j<T} b_j x^j`. -/
noncomputable def PT (T : ℕ) (x : ℝ) : ℝ := ∑ j ∈ Finset.range T, bB j * x ^ j

/-- The derivative of `P_T`. -/
noncomputable def dPT (T : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range T, bB j * ((j : ℝ) * x ^ (j - 1))

lemma hasDerivAt_PT (T : ℕ) (x : ℝ) : HasDerivAt (PT T) (dPT T x) x := by
  unfold PT dPT
  exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_pow j x).const_mul (bB j)

/-- **The telescoping identity** `−P_T + 2(1 − x)·P_T′ = −2T·b_T·x^{T−1}`. -/
lemma PT_tel (T : ℕ) (x : ℝ) :
    -PT T x + 2 * (1 - x) * dPT T x = -(2 * (T : ℝ) * bB T * x ^ (T - 1)) := by
  induction T with
  | zero => simp [PT, dPT]
  | succ T ih =>
    have e1 : PT (T + 1) x = PT T x + bB T * x ^ T := by
      unfold PT; rw [Finset.sum_range_succ]
    have e2 : dPT (T + 1) x = dPT T x + bB T * ((T : ℝ) * x ^ (T - 1)) := by
      unfold dPT; rw [Finset.sum_range_succ]
    rw [e1, e2, bB_succ]
    have h3 : (2 * (T : ℝ) + 2) ≠ 0 := by positivity
    have e3 : (T : ℝ) * x ^ (T - 1) * x = (T : ℝ) * x ^ T := by
      rcases Nat.eq_zero_or_pos T with h | h
      · subst h; simp
      · have : x ^ (T - 1) * x = x ^ T := by
          rw [← pow_succ]
          congr 1
          omega
        rw [mul_assoc, this]
    have e4 : -(PT T x + bB T * x ^ T) + 2 * (1 - x) * (dPT T x + bB T * ((T : ℝ) * x ^ (T - 1))) =
        (-PT T x + 2 * (1 - x) * dPT T x) - bB T * x ^ T +
          2 * bB T * ((T : ℝ) * x ^ (T - 1)) - 2 * bB T * ((T : ℝ) * x ^ (T - 1) * x) := by ring
    rw [e4, ih, e3]
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

lemma PT_zero_arg {T : ℕ} (hT : 1 ≤ T) : PT T 0 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
  unfold PT
  rw [Finset.sum_range_succ']
  simp [bB_zero]

lemma PT_nonneg (T : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ PT T x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (bB_pos j).le (pow_nonneg hx j)

/-- The derivative of `x ↦ √(1 − x)·P_T(x)` for `x < 1`: `−T·b_T·x^{T−1}/√(1 − x)`. -/
lemma hasDerivAt_FT (T : ℕ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y => √(1 - y) * PT T y)
      (-((T : ℝ) * bB T * x ^ (T - 1)) / √(1 - x)) x := by
  have h1x : 0 < 1 - x := by linarith
  have hs : 0 < √(1 - x) := Real.sqrt_pos.mpr h1x
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have h2 := h1.sqrt h1x.ne'
  have h3 := h2.mul (hasDerivAt_PT T x)
  refine h3.congr_deriv ?_
  have htel := PT_tel T x
  have hsq : √(1 - x) * √(1 - x) = 1 - x := Real.mul_self_sqrt h1x.le
  rw [eq_div_iff hs.ne']
  have e5 : (-1 / (2 * √(1 - x)) * PT T x + √(1 - x) * dPT T x) * √(1 - x) =
      (-PT T x + 2 * (√(1 - x) * √(1 - x)) * dPT T x) / 2 := by
    field_simp
  rw [e5, hsq, htel]
  ring

/-- **The partial sums of the series of `(1 − x)^{−1/2}`**: for `T ≥ 1` and `0 ≤ x < 1`:
`1/√(1 − x) − b_T·x^T/(1 − x) ≤ P_T(x) ≤ 1/√(1 − x)`. -/
theorem PT_bounds {T : ℕ} (hT : 1 ≤ T) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    1 / √(1 - x) - bB T * x ^ T / (1 - x) ≤ PT T x ∧ PT T x ≤ 1 / √(1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have hs : 0 < √(1 - x) := Real.sqrt_pos.mpr h1x
  have hsq : √(1 - x) * √(1 - x) = 1 - x := Real.mul_self_sqrt h1x.le
  have hb := bB_pos T
  -- upper: `y ↦ −√(1 − y)·P_T(y)` is monotone
  have hup : √(1 - x) * PT T x ≤ 1 := by
    have h := le_of_hasDeriv_nonneg (f := fun y => -(√(1 - y) * PT T y))
      (f' := fun y => -(-((T : ℝ) * bB T * y ^ (T - 1)) / √(1 - y))) hx0
      (fun y hy => (hasDerivAt_FT T (lt_of_le_of_lt hy.2 hx1)).neg)
      (fun y hy => by
        have h1y : 0 < 1 - y := by linarith [hy.2]
        have hsy : 0 < √(1 - y) := Real.sqrt_pos.mpr h1y
        have hy0 : 0 ≤ y := hy.1.le
        rw [neg_div, neg_neg]
        positivity)
    simp only [sub_zero, Real.sqrt_one, one_mul, PT_zero_arg hT] at h
    linarith
  -- lower: `y ↦ √(1 − y)·P_T(y) + b_T·y^T/√(1 − x)` is monotone on `[0, x]`
  have hlow : 1 ≤ √(1 - x) * PT T x + bB T * x ^ T / √(1 - x) := by
    have hd : ∀ y ∈ Icc 0 x, HasDerivAt (fun y => √(1 - y) * PT T y + bB T * y ^ T / √(1 - x))
        (-((T : ℝ) * bB T * y ^ (T - 1)) / √(1 - y) +
          bB T * ((T : ℝ) * y ^ (T - 1)) / √(1 - x)) y := by
      intro y hy
      exact (hasDerivAt_FT T (lt_of_le_of_lt hy.2 hx1)).add
        (((hasDerivAt_pow T y).const_mul (bB T)).div_const _)
    have h := le_of_hasDeriv_nonneg hx0 hd (fun y hy => by
      have h1y : 0 < 1 - y := by linarith [hy.2]
      have hsy : 0 < √(1 - y) := Real.sqrt_pos.mpr h1y
      have hy0 : 0 ≤ y := hy.1.le
      have hle : √(1 - x) ≤ √(1 - y) := Real.sqrt_le_sqrt (by linarith [hy.2])
      have hnum : 0 ≤ (T : ℝ) * bB T * y ^ (T - 1) := by positivity
      have e : -((T : ℝ) * bB T * y ^ (T - 1)) / √(1 - y) +
          bB T * ((T : ℝ) * y ^ (T - 1)) / √(1 - x) =
          (T : ℝ) * bB T * y ^ (T - 1) * (1 / √(1 - x) - 1 / √(1 - y)) := by ring
      rw [e]
      have : 1 / √(1 - y) ≤ 1 / √(1 - x) := one_div_le_one_div_of_le hs hle
      exact mul_nonneg hnum (by linarith))
    simp only [sub_zero, Real.sqrt_one, one_mul, PT_zero_arg hT] at h
    have h0 : (0 : ℝ) ^ T = 0 := zero_pow (by omega)
    rw [h0, mul_zero, zero_div, add_zero] at h
    exact h
  constructor
  · have e : 1 / √(1 - x) - bB T * x ^ T / (1 - x) =
        (1 - bB T * x ^ T / √(1 - x)) / √(1 - x) := by
      rw [sub_div, div_div, hsq]
    rw [e, div_le_iff₀ hs]
    linarith
  · rw [le_div_iff₀ hs]
    linarith

/-! ## The inverse sine -/

lemma QTsum_eq (T : ℕ) (v : ℝ) :
    QTsum T v = ∑ j ∈ Finset.range T, bB j * v ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
  unfold QTsum bB
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma QTsum_zero_arg (T : ℕ) : QTsum T 0 = 0 := by
  rw [QTsum_eq]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp

/-- The derivative of `Q_T` is `P_T(v²)`. -/
lemma hasDerivAt_QTsum (T : ℕ) (v : ℝ) : HasDerivAt (QTsum T) (PT T (v ^ 2)) v := by
  have e : QTsum T = fun v => ∑ j ∈ Finset.range T,
      bB j * v ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := funext (QTsum_eq T)
  rw [e]
  unfold PT
  refine (HasDerivAt.fun_sum fun j _ =>
    ((hasDerivAt_pow (2 * j + 1) v).const_mul (bB j)).div_const (2 * (j : ℝ) + 1)).congr_deriv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [pow_mul]
  field_simp

/-- **The partial sum of the inverse sine series against the inverse sine**: for `T ≥ 1` and
`0 ≤ v < 1`: `0 ≤ arcsin v − Q_T(v) ≤ v·(v²)^T/(1 − v²)`. -/
theorem QTsum_err {T : ℕ} (hT : 1 ≤ T) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    0 ≤ arcsin v - QTsum T v ∧ arcsin v - QTsum T v ≤ v * (v ^ 2) ^ T / (1 - v ^ 2) := by
  have h1v : 0 < 1 - v ^ 2 := by nlinarith
  have hE : ∀ y ∈ Icc 0 v, HasDerivAt (fun y => arcsin y - QTsum T y)
      (1 / √(1 - y ^ 2) - PT T (y ^ 2)) y := by
    intro y hy
    exact (Real.hasDerivAt_arcsin (by linarith [hy.1]) (by linarith [hy.2])).sub
      (hasDerivAt_QTsum T y)
  have hy2 : ∀ y ∈ Icc 0 v, 0 ≤ y ^ 2 ∧ y ^ 2 < 1 := fun y hy =>
    ⟨sq_nonneg y, by nlinarith [hy.1, hy.2]⟩
  constructor
  · have h := le_of_hasDeriv_nonneg hv0 hE (fun y hy => by
      obtain ⟨a, b⟩ := hy2 y (Ioo_subset_Icc_self hy)
      have := (PT_bounds hT a b).2
      linarith)
    simp only [Real.arcsin_zero, QTsum_zero_arg, sub_zero] at h
    exact h
  · have hK : ∀ y ∈ Icc 0 v, HasDerivAt
        (fun y => y ^ (2 * T + 1) / ((2 * (T : ℝ) + 1) * (1 - v ^ 2)) - (arcsin y - QTsum T y))
        (((2 * T + 1 : ℕ) : ℝ) * y ^ (2 * T + 1 - 1) / ((2 * (T : ℝ) + 1) * (1 - v ^ 2)) -
          (1 / √(1 - y ^ 2) - PT T (y ^ 2))) y := by
      intro y hy
      exact ((hasDerivAt_pow (2 * T + 1) y).div_const _).sub (hE y hy)
    have h := le_of_hasDeriv_nonneg hv0 hK (fun y hy => by
      have hyI := Ioo_subset_Icc_self hy
      obtain ⟨a, b⟩ := hy2 y hyI
      have hlow := (PT_bounds hT a b).1
      have h1y : 0 < 1 - y ^ 2 := by linarith
      have hT0 : (0 : ℝ) < 2 * (T : ℝ) + 1 := by positivity
      have e1 : ((2 * T + 1 : ℕ) : ℝ) * y ^ (2 * T + 1 - 1) /
          ((2 * (T : ℝ) + 1) * (1 - v ^ 2)) = (y ^ 2) ^ T / (1 - v ^ 2) := by
        simp only [Nat.add_sub_cancel]
        push_cast
        rw [pow_mul]
        field_simp
      rw [e1]
      have hb : bB T * (y ^ 2) ^ T / (1 - y ^ 2) ≤ (y ^ 2) ^ T / (1 - v ^ 2) := by
        have hp : 0 ≤ (y ^ 2) ^ T := by positivity
        have h3 : bB T * (y ^ 2) ^ T ≤ (y ^ 2) ^ T := by
          have := mul_le_mul_of_nonneg_right (bB_le_one T) hp
          linarith
        have h4 : 1 - v ^ 2 ≤ 1 - y ^ 2 := by nlinarith [hyI.1, hyI.2]
        exact div_le_div₀ hp h3 h1v h4
      linarith)
    simp only [Real.arcsin_zero, QTsum_zero_arg, sub_zero] at h
    have h0 : (0 : ℝ) ^ (2 * T + 1) = 0 := zero_pow (by omega)
    rw [h0, zero_div] at h
    have hT0 : (0 : ℝ) < 2 * (T : ℝ) + 1 := by positivity
    have h5 : v ^ (2 * T + 1) / ((2 * (T : ℝ) + 1) * (1 - v ^ 2)) ≤
        v * (v ^ 2) ^ T / (1 - v ^ 2) := by
      have e : v ^ (2 * T + 1) = v * (v ^ 2) ^ T := by rw [pow_succ, pow_mul]; ring
      rw [e]
      refine div_le_div_of_nonneg_left (by positivity) h1v ?_
      nlinarith
    linarith

end BstLean.Part159

open BstLean.Part159 in
#print axioms PT_tel
open BstLean.Part159 in
#print axioms PT_bounds
open BstLean.Part159 in
#print axioms QTsum_err
