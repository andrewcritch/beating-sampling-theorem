import BstLean.Part161Cor

/-!
# Part 161, item 1(c): the centred sixth-order bound of the chi-square (formula `t7:p07:chi-six`)

Role: `delegations/statements/p161-spec.md`, item 1(c). Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Corollary `t7:p07:chi-bounds`,
formula `t7:p07:chi-six` (the form used by Proposition `t7:p07:FL`).

* `exp_le_six`: `e^T ≤ Σ_{j ≤ 5} T^j/j! + e^{max(T, 0)}·T⁶/720`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open scoped Nat

/-- For `y ≥ 0`: `1 ≤ S₇(y)·P₆(−y)`, `S₇` and `P₆` the Taylor polynomials of `e^y` and `e^{−y}`
(all coefficients of the product above degree `0` are `≥ 0`). -/
lemma taylor_prod_ge (y : ℝ) (hy : 0 ≤ y) :
    1 ≤ (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720 + y ^ 7 / 5040) *
      (1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720) := by
  have e : (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720 + y ^ 7 / 5040) *
      (1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720) =
      1 + y ^ 7 / 5040 + 6 * y ^ 8 / 40320 + 36 * y ^ 9 / 362880 + 48 * y ^ 10 / 3628800 +
        330 * y ^ 11 / 39916800 + 132 * y ^ 12 / 479001600 + 1716 * y ^ 13 / 6227020800 := by
    ring
  rw [e]
  have := pow_nonneg hy 7
  have := pow_nonneg hy 8
  have := pow_nonneg hy 9
  have := pow_nonneg hy 10
  have := pow_nonneg hy 11
  have := pow_nonneg hy 12
  have := pow_nonneg hy 13
  linarith

/-- **The sixth-order exponential bound** `e^T ≤ Σ_{j ≤ 5} T^j/j! + e^{max(T, 0)}·T⁶/720`. -/
lemma exp_le_six (T : ℝ) :
    exp T ≤ 1 + T + T ^ 2 / 2 + T ^ 3 / 6 + T ^ 4 / 24 + T ^ 5 / 120 +
      exp (max T 0) * T ^ 6 / 720 := by
  rcases le_total 0 T with hT | hT
  · rw [max_eq_left hT]
    have hS := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) T
    rw [← Real.exp_eq_exp_ℝ] at hS
    have hT6 := (hasSum_nat_add_iff' (f := fun n : ℕ => T ^ n / (n ! : ℝ)) 6).mpr hS
    have e6 : ∑ i ∈ Finset.range 6, T ^ i / (i ! : ℝ) =
        1 + T + T ^ 2 / 2 + T ^ 3 / 6 + T ^ 4 / 24 + T ^ 5 / 120 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
      norm_num
    rw [e6] at hT6
    have hG := hS.mul_left (T ^ 6 / 720)
    have hle : ∀ k : ℕ, T ^ (k + 6) / ((k + 6)! : ℝ) ≤ T ^ 6 / 720 * (T ^ k / (k ! : ℝ)) := by
      intro k
      have hf : (720 : ℝ) * (k ! : ℝ) ≤ ((k + 6)! : ℝ) := by
        have : 720 * k ! ≤ (k + 6)! := by
          have h := Nat.le_of_dvd (Nat.factorial_pos _)
            (Nat.factorial_mul_factorial_dvd_factorial_add k 6)
          have h6 : (6 : ℕ)! = 720 := by decide
          rw [h6] at h; linarith
        exact_mod_cast this
      have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hpow : 0 ≤ T ^ (k + 6) := pow_nonneg hT _
      rw [show T ^ 6 / 720 * (T ^ k / (k ! : ℝ)) = T ^ (k + 6) / (720 * (k ! : ℝ)) by
        rw [pow_add]; field_simp]
      exact div_le_div_of_nonneg_left hpow (by positivity) hf
    have hsum := hasSum_le hle hT6 hG
    nlinarith
  · rw [max_eq_right hT, exp_zero, one_mul]
    set y := -T with hy
    have hy0 : 0 ≤ y := by rw [hy]; linarith
    have hE := Real.sum_le_exp_of_nonneg hy0 8
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
      Nat.factorial, Nat.cast_one, div_one, zero_add, pow_one, Nat.succ_eq_add_one] at hE
    norm_num at hE
    have hP := taylor_prod_ge y hy0
    have hS7 : 0 < 1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 + y ^ 6 / 720 +
        y ^ 7 / 5040 := by positivity
    have he : exp T = (exp y)⁻¹ := by rw [hy, Real.exp_neg, inv_inv]
    rw [he]
    have hex : 0 < exp y := exp_pos y
    rw [inv_le_iff_one_le_mul₀ hex]
    have e2 : 1 + T + T ^ 2 / 2 + T ^ 3 / 6 + T ^ 4 / 24 + T ^ 5 / 120 + T ^ 6 / 720 =
        1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720 := by
      rw [hy]; ring
    rw [e2]
    have hP6 : 0 < 1 - y + y ^ 2 / 2 - y ^ 3 / 6 + y ^ 4 / 24 - y ^ 5 / 120 + y ^ 6 / 720 := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hS7.le]
    have := mul_le_mul_of_nonneg_right hE hP6.le
    nlinarith

/-- **The pointwise parts of `T = log kTwo`** in the window: `T ≤ L` (the first-order terms and
the corrections) and `|T| ≤ B₁ + B₂ + B₃ + B₄` with `B₁ = κ(n/2)|ε||ε'|`, `B₂ = κa²|δ||δ'|`,
`B₃ = κ(a²/2)δ₀|δ||ε'|`, `B₄ = κ(a²/2)δ₀|ε||δ'|`. -/
theorem T_parts (n : ℕ) {a2 δ ε δ' ε' ε₀ δ₀ : ℝ} (ha : 0 ≤ a2) (hε₀ : ε₀ < 1)
    (hε : |ε| ≤ ε₀) (hε' : |ε'| ≤ ε₀) (hδ : |δ| ≤ δ₀) (hδ' : |δ'| ≤ δ₀) :
    log (kTwo n a2 δ ε δ' ε') ≤
      n / 2 * (ε * ε') + n * (1 - ε₀ ^ 2)⁻¹ / 4 * (ε ^ 2 * ε' ^ 2) + a2 * (δ * δ') +
        a2 * (1 - ε₀ ^ 2)⁻¹ * ((|δ| * |ε|) * (|δ'| * |ε'|)) + a2 / 2 * (δ ^ 2 * ε') +
        a2 / 2 * (ε * δ' ^ 2) + a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * ((δ ^ 2 * |ε|) * ε' ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * (ε ^ 2 * (δ' ^ 2 * |ε'|)) ∧
    |log (kTwo n a2 δ ε δ' ε')| ≤
      (1 - ε₀ ^ 2)⁻¹ * (n / 2) * (|ε| * |ε'|) + (1 - ε₀ ^ 2)⁻¹ * a2 * (|δ| * |δ'|) +
        (1 - ε₀ ^ 2)⁻¹ * (a2 / 2 * δ₀) * (|δ| * |ε'|) +
        (1 - ε₀ ^ 2)⁻¹ * (a2 / 2 * δ₀) * (|ε| * |δ'|) := by
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans hε
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans hδ
  set r := ε₀ ^ 2 with hr
  have hr1 : r < 1 := by rw [hr]; nlinarith
  have hr0 : 0 < 1 - r := by linarith
  set κ := (1 - r)⁻¹ with hκ
  have hκ1 : 1 ≤ κ := by rw [hκ]; exact one_le_inv₀ hr0 |>.mpr (by nlinarith)
  have hκ0 : 0 < κ := by linarith
  set w := ε * ε' with hw
  have haw : |w| = |ε| * |ε'| := abs_mul _ _
  have hwr : |w| ≤ r := by rw [haw, hr, sq]; exact mul_le_mul hε hε' (abs_nonneg _) hε0
  have hD : 0 < 1 - w := by linarith [le_abs_self w]
  set u := (1 - w)⁻¹ with hu
  have hu0 : 0 < u := inv_pos.mpr hD
  have huκ : u ≤ κ := inv_anti₀ hr0 (by linarith [le_abs_self w])
  have hu1 : u - 1 = w * u := by rw [hu]; field_simp; ring
  have hu1abs : |u - 1| ≤ κ * |w| := by
    rw [hu1, abs_mul, abs_of_pos hu0, mul_comm]
    exact mul_le_mul_of_nonneg_right huκ (abs_nonneg _)
  -- the four parts of `T`
  set A1 := (n : ℝ) / 2 * (-log (1 - w)) with hA1
  set A2 := a2 * (δ * δ') * u with hA2
  set A3 := a2 / 2 * (δ ^ 2 * ε') * u with hA3
  set A4 := a2 / 2 * (δ' ^ 2 * ε) * u with hA4
  have hT : kTwo n a2 δ ε δ' ε' = exp (A1 + A2 + A3 + A4) := by
    have hD' : 1 - ε * ε' ≠ 0 := by rw [← hw]; exact hD.ne'
    rw [kTwo_eq_exp n a2 δ ε δ' ε' (by rw [← hw]; exact hD)]
    congr 1
    rw [hA1, hA2, hA3, hA4, hu, hw]
    field_simp
    ring
  set T := A1 + A2 + A3 + A4 with hTd
  clear_value T A1 A2 A3 A4 u
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- upper bounds
  have b1 : A1 ≤ n / 2 * w + n * κ / 4 * (ε ^ 2 * ε' ^ 2) := by
    have := neg_log_le hwr hr1
    have e : w ^ 2 / (2 * (1 - r)) = κ / 2 * (ε ^ 2 * ε' ^ 2) := by
      rw [hκ, hw]; field_simp
    rw [e] at this
    rw [hA1]
    nlinarith
  have habs1 : ∀ x y : ℝ, x * (u - 1) ≤ |x| * (κ * |w|) := fun x y => by
    calc x * (u - 1) ≤ |x * (u - 1)| := le_abs_self _
      _ = |x| * |u - 1| := abs_mul _ _
      _ ≤ |x| * (κ * |w|) := mul_le_mul_of_nonneg_left hu1abs (abs_nonneg _)
  have b2 : A2 ≤ a2 * (δ * δ') + a2 * κ * ((|δ| * |ε|) * (|δ'| * |ε'|)) := by
    have e : A2 = a2 * (δ * δ') + a2 * (δ * δ') * (u - 1) := by rw [hA2]; ring
    have h := habs1 (a2 * (δ * δ')) 0
    rw [abs_mul, abs_mul, abs_of_nonneg ha, haw] at h
    have e2 : a2 * (|δ| * |δ'|) * (κ * (|ε| * |ε'|)) =
        a2 * κ * ((|δ| * |ε|) * (|δ'| * |ε'|)) := by ring
    rw [e]; linarith
  have b3 : A3 ≤ a2 / 2 * (δ ^ 2 * ε') + a2 * κ / 2 * ((δ ^ 2 * |ε|) * ε' ^ 2) := by
    have e : A3 = a2 / 2 * (δ ^ 2 * ε') + a2 / 2 * (δ ^ 2 * ε') * (u - 1) := by rw [hA3]; ring
    have h := habs1 (a2 / 2 * (δ ^ 2 * ε')) 0
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a2 / 2),
      abs_of_nonneg (sq_nonneg δ), haw] at h
    have e2 : |ε'| * |ε'| = ε' ^ 2 := by rw [← sq, sq_abs]
    have e3 : a2 / 2 * (δ ^ 2 * |ε'|) * (κ * (|ε| * |ε'|)) =
        a2 * κ / 2 * ((δ ^ 2 * |ε|) * ε' ^ 2) := by rw [← e2]; ring
    rw [e]; linarith
  have b4 : A4 ≤ a2 / 2 * (ε * δ' ^ 2) + a2 * κ / 2 * (ε ^ 2 * (δ' ^ 2 * |ε'|)) := by
    have e : A4 = a2 / 2 * (ε * δ' ^ 2) + a2 / 2 * (δ' ^ 2 * ε) * (u - 1) := by rw [hA4]; ring
    have h := habs1 (a2 / 2 * (δ' ^ 2 * ε)) 0
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a2 / 2),
      abs_of_nonneg (sq_nonneg δ'), haw] at h
    have e2 : |ε| * |ε| = ε ^ 2 := by rw [← sq, sq_abs]
    have e3 : a2 / 2 * (δ' ^ 2 * |ε|) * (κ * (|ε| * |ε'|)) =
        a2 * κ / 2 * (ε ^ 2 * (δ' ^ 2 * |ε'|)) := by rw [← e2]; ring
    rw [e]; linarith
  -- absolute bounds
  have hl := abs_log_le hwr hr1
  have c1 : |A1| ≤ n / 2 * (κ * |w|) := by
    rw [hA1, abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hκ, mul_comm, ← div_eq_mul_inv]; exact hl
  have hdd : |δ| * |δ'| ≤ δ₀ ^ 2 := by rw [sq]; exact mul_le_mul hδ hδ' (abs_nonneg _) hδ0
  have hd2 : δ ^ 2 ≤ δ₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have hd2' : δ' ^ 2 ≤ δ₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ' 2
  have c2 : |A2| ≤ a2 * |δ| * |δ'| * u := by
    rw [hA2, abs_mul, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos hu0]; ring_nf; rfl
  have c3 : |A3| ≤ a2 / 2 * δ ^ 2 * |ε'| * u := by
    rw [hA3, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a2 / 2),
      abs_of_nonneg (sq_nonneg δ), abs_of_pos hu0]
    exact le_of_eq (by ring)
  have c4 : |A4| ≤ a2 / 2 * δ' ^ 2 * |ε| * u := by
    rw [hA4, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a2 / 2),
      abs_of_nonneg (sq_nonneg δ'), abs_of_pos hu0]
    exact le_of_eq (by ring)
  have hlog : log (kTwo n a2 δ ε δ' ε') = T := by rw [hT, Real.log_exp]
  rw [hlog]
  refine ⟨by rw [hTd]; linarith, ?_⟩
  have d3 : δ ^ 2 ≤ δ₀ * |δ| := by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  have d4 : δ' ^ 2 ≤ δ₀ * |δ'| := by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_right hδ' (abs_nonneg _)
  have e1 : |A1| ≤ κ * (n / 2) * (|ε| * |ε'|) := by
    have := c1; rw [haw] at this; linarith [show (n : ℝ) / 2 * (κ * (|ε| * |ε'|)) =
      κ * (n / 2) * (|ε| * |ε'|) by ring]
  have e2 : |A2| ≤ κ * a2 * (|δ| * |δ'|) := by
    refine c2.trans ?_
    have h := mul_le_mul_of_nonneg_left huκ (mul_nonneg (mul_nonneg ha (abs_nonneg δ))
      (abs_nonneg δ'))
    linarith [show a2 * |δ| * |δ'| * κ = κ * a2 * (|δ| * |δ'|) by ring]
  have e3 : |A3| ≤ κ * (a2 / 2 * δ₀) * (|δ| * |ε'|) := by
    refine c3.trans ?_
    have h1 : a2 / 2 * δ ^ 2 * |ε'| ≤ a2 / 2 * (δ₀ * |δ|) * |ε'| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d3 (by positivity)) (abs_nonneg _)
    have h2 := mul_le_mul h1 huκ hu0.le (by positivity)
    linarith [show a2 / 2 * (δ₀ * |δ|) * |ε'| * κ = κ * (a2 / 2 * δ₀) * (|δ| * |ε'|) by ring]
  have e4 : |A4| ≤ κ * (a2 / 2 * δ₀) * (|ε| * |δ'|) := by
    refine c4.trans ?_
    have h1 : a2 / 2 * δ' ^ 2 * |ε| ≤ a2 / 2 * (δ₀ * |δ'|) * |ε| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d4 (by positivity)) (abs_nonneg _)
    have h2 := mul_le_mul h1 huκ hu0.le (by positivity)
    linarith [show a2 / 2 * (δ₀ * |δ'|) * |ε| * κ = κ * (a2 / 2 * δ₀) * (|ε| * |δ'|) by ring]
  have s1 := abs_add_le (A1 + A2 + A3) A4
  have s2 := abs_add_le (A1 + A2) A3
  have s3 := abs_add_le A1 A2
  rw [hTd]
  linarith

/-- The weighted power mean for four terms: for `x_i ≥ 0`, `c_i > 0`, `C = Σ c_i`:
`(Σ x_i)^k ≤ C^{k−1}·Σ x_i^k/c_i^{k−1}`, written with `C^k·Σ (c_i/C)(x_i/c_i)^k`. -/
lemma pow4_le (k : ℕ) {x1 x2 x3 x4 c1 c2 c3 c4 : ℝ} (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (h4 : 0 ≤ x4) (p1 : 0 < c1) (p2 : 0 < c2) (p3 : 0 < c3) (p4 : 0 < c4) :
    (x1 + x2 + x3 + x4) ^ k ≤ (c1 + c2 + c3 + c4) ^ k *
      (c1 / (c1 + c2 + c3 + c4) * (x1 / c1) ^ k + c2 / (c1 + c2 + c3 + c4) * (x2 / c2) ^ k +
        c3 / (c1 + c2 + c3 + c4) * (x3 / c3) ^ k + c4 / (c1 + c2 + c3 + c4) * (x4 / c4) ^ k) := by
  set C := c1 + c2 + c3 + c4 with hC
  have hC0 : 0 < C := by positivity
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin 4))
    ![c1 / C, c2 / C, c3 / C, c4 / C] ![x1 * C / c1, x2 * C / c2, x3 * C / c3, x4 * C / c4]
    (fun i _ => by fin_cases i <;> simp <;> positivity)
    (by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [← add_div, ← add_div, ← add_div, ← hC, div_self hC0.ne'])
    (fun i _ => by fin_cases i <;> simp <;> positivity) k
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
  have e1 : c1 / C * (x1 * C / c1) + c2 / C * (x2 * C / c2) + c3 / C * (x3 * C / c3) +
      c4 / C * (x4 * C / c4) = x1 + x2 + x3 + x4 := by field_simp
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  have e2 : ∀ (x c : ℝ), 0 < c → c / C * (x * C / c) ^ k = C ^ k * (c / C * (x / c) ^ k) := by
    intro x c hc
    rw [show x * C / c = C * (x / c) by field_simp, mul_pow]; ring
  rw [e2 x1 c1 p1, e2 x2 c2 p2, e2 x3 c3 p3, e2 x4 c4 p4]
  ring

section moments

variable {α : Type*} [MeasurableSpace α]

/-- **Minkowski's inequality for four nonnegative bounded functions** (in the form used for
`‖T‖_k ≤ 𝒯_k`): if `E g_i^k ≤ b_i^k` with `b_i ≥ 0`, then `E (Σ g_i)^k ≤ (Σ b_i)^k`. -/
theorem mink4 (μ : Measure α) [IsProbabilityMeasure μ] (k : ℕ) {g1 g2 g3 g4 : α → ℝ}
    (m1 : Measurable g1) (m2 : Measurable g2) (m3 : Measurable g3) (m4 : Measurable g4)
    (n1 : ∀ x, 0 ≤ g1 x) (n2 : ∀ x, 0 ≤ g2 x) (n3 : ∀ x, 0 ≤ g3 x) (n4 : ∀ x, 0 ≤ g4 x)
    {M : ℝ} (B1 : ∀ x, g1 x ≤ M) (B2 : ∀ x, g2 x ≤ M) (B3 : ∀ x, g3 x ≤ M) (B4 : ∀ x, g4 x ≤ M)
    {b1 b2 b3 b4 : ℝ} (q1 : 0 ≤ b1) (q2 : 0 ≤ b2) (q3 : 0 ≤ b3) (q4 : 0 ≤ b4)
    (I1 : ∫ x, g1 x ^ k ∂μ ≤ b1 ^ k) (I2 : ∫ x, g2 x ^ k ∂μ ≤ b2 ^ k)
    (I3 : ∫ x, g3 x ^ k ∂μ ≤ b3 ^ k) (I4 : ∫ x, g4 x ^ k ∂μ ≤ b4 ^ k) :
    ∫ x, (g1 x + g2 x + g3 x + g4 x) ^ k ∂μ ≤ (b1 + b2 + b3 + b4) ^ k := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have ipow : ∀ {f : α → ℝ}, Measurable f → (∀ x, 0 ≤ f x) → ∀ K : ℝ, (∀ x, f x ≤ K) →
      Integrable (fun x => f x ^ k) μ := fun {f} hf h0 K hB =>
    Integrable.of_bound (hf.pow_const k).aestronglyMeasurable (K ^ k)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h0 x) k)]
        exact pow_le_pow_left₀ (h0 x) (hB x) k)
  have iS : Integrable (fun x => (g1 x + g2 x + g3 x + g4 x) ^ k) μ :=
    ipow (f := fun x => g1 x + g2 x + g3 x + g4 x) (((m1.add m2).add m3).add m4)
      (fun x => by linarith [n1 x, n2 x, n3 x, n4 x])
      (4 * M) (fun x => by linarith [B1 x, B2 x, B3 x, B4 x])
  have i1 := ipow m1 n1 M B1
  have i2 := ipow m2 n2 M B2
  have i3 := ipow m3 n3 M B3
  have i4 := ipow m4 n4 M B4
  set S := ∫ x, (g1 x + g2 x + g3 x + g4 x) ^ k ∂μ
  have key : ∀ η : ℝ, 0 < η → S ≤ (b1 + b2 + b3 + b4 + 4 * η) ^ k := by
    intro η hη
    set c1 := b1 + η
    set c2 := b2 + η
    set c3 := b3 + η
    set c4 := b4 + η
    have p1 : 0 < c1 := by positivity
    have p2 : 0 < c2 := by positivity
    have p3 : 0 < c3 := by positivity
    have p4 : 0 < c4 := by positivity
    set C := c1 + c2 + c3 + c4 with hC
    have hC0 : 0 < C := by positivity
    have hCe : C = b1 + b2 + b3 + b4 + 4 * η := by rw [hC]; ring
    have hpt : ∀ x, (g1 x + g2 x + g3 x + g4 x) ^ k ≤ C ^ k * (c1 / C * (g1 x ^ k / c1 ^ k) +
        c2 / C * (g2 x ^ k / c2 ^ k) + c3 / C * (g3 x ^ k / c3 ^ k) +
        c4 / C * (g4 x ^ k / c4 ^ k)) := fun x => by
      have h := pow4_le k (n1 x) (n2 x) (n3 x) (n4 x) p1 p2 p3 p4
      simp only [div_pow] at h
      exact h
    have iR : Integrable (fun x => C ^ k * (c1 / C * (g1 x ^ k / c1 ^ k) +
        c2 / C * (g2 x ^ k / c2 ^ k) + c3 / C * (g3 x ^ k / c3 ^ k) +
        c4 / C * (g4 x ^ k / c4 ^ k))) μ := by
      refine Integrable.const_mul ?_ _
      exact ((((i1.div_const _).const_mul _).add ((i2.div_const _).const_mul _)).add
        ((i3.div_const _).const_mul _)).add ((i4.div_const _).const_mul _)
    have h := integral_mono iS iR hpt
    have hR : ∫ x, C ^ k * (c1 / C * (g1 x ^ k / c1 ^ k) +
        c2 / C * (g2 x ^ k / c2 ^ k) + c3 / C * (g3 x ^ k / c3 ^ k) +
        c4 / C * (g4 x ^ k / c4 ^ k)) ∂μ = C ^ k * (c1 / C * ((∫ x, g1 x ^ k ∂μ) / c1 ^ k) +
        c2 / C * ((∫ x, g2 x ^ k ∂μ) / c2 ^ k) + c3 / C * ((∫ x, g3 x ^ k ∂μ) / c3 ^ k) +
        c4 / C * ((∫ x, g4 x ^ k ∂μ) / c4 ^ k)) := by
      rw [integral_const_mul]
      congr 1
      repeat rw [integral_add]
      all_goals try fun_prop
      · simp only [integral_const_mul, integral_div]
      all_goals first
        | exact (i1.div_const _).const_mul _
        | exact (i2.div_const _).const_mul _
        | exact (i3.div_const _).const_mul _
        | exact (i4.div_const _).const_mul _
        | exact ((i1.div_const _).const_mul _).add ((i2.div_const _).const_mul _)
        | exact (((i1.div_const _).const_mul _).add ((i2.div_const _).const_mul _)).add
            ((i3.div_const _).const_mul _)
    rw [hR] at h
    have r : ∀ (b c I : ℝ), 0 ≤ b → b ≤ c → 0 < c → I ≤ b ^ k → c / C * (I / c ^ k) ≤ c / C :=
      fun b c I hb hbc hc hI => by
        have hck : 0 < c ^ k := pow_pos hc k
        have : I / c ^ k ≤ 1 := by
          rw [div_le_one hck]; exact hI.trans (pow_le_pow_left₀ hb hbc k)
        calc c / C * (I / c ^ k) ≤ c / C * 1 :=
              mul_le_mul_of_nonneg_left this (div_nonneg hc.le hC0.le)
          _ = c / C := mul_one _
    have r1 := r b1 c1 _ q1 (by linarith) p1 I1
    have r2 := r b2 c2 _ q2 (by linarith) p2 I2
    have r3 := r b3 c3 _ q3 (by linarith) p3 I3
    have r4 := r b4 c4 _ q4 (by linarith) p4 I4
    have hsum : c1 / C + c2 / C + c3 / C + c4 / C = 1 := by
      rw [← add_div, ← add_div, ← add_div, ← hC, div_self hC0.ne']
    have hCk : 0 ≤ C ^ k := pow_nonneg hC0.le k
    have := mul_le_mul_of_nonneg_left (show c1 / C * ((∫ x, g1 x ^ k ∂μ) / c1 ^ k) +
      c2 / C * ((∫ x, g2 x ^ k ∂μ) / c2 ^ k) + c3 / C * ((∫ x, g3 x ^ k ∂μ) / c3 ^ k) +
      c4 / C * ((∫ x, g4 x ^ k ∂μ) / c4 ^ k) ≤ 1 by linarith) hCk
    rw [← hCe]
    linarith
  have ht : Filter.Tendsto (fun η : ℝ => (b1 + b2 + b3 + b4 + 4 * η) ^ k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((b1 + b2 + b3 + b4) ^ k)) := by
    have hc : Continuous (fun η : ℝ => (b1 + b2 + b3 + b4 + 4 * η) ^ k) := by fun_prop
    have := hc.tendsto 0
    simp only [mul_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun η hη => key η hη)

end moments

/-- `(E|f|³)² ≤ E f² · E f⁴` and `(E|f|⁵)² ≤ E f⁴ · E f⁶` for a bounded measurable `f`. -/
lemma cs_odd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    (∫ x, |f x| ^ 3 ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, f x ^ 4 ∂μ ∧
      (∫ x, |f x| ^ 5 ∂μ) ^ 2 ≤ (∫ x, f x ^ 4 ∂μ) * ∫ x, f x ^ 6 ∂μ := by
  have ia : ∀ j : ℕ, Integrable (fun x => |f x| ^ j) μ := fun j =>
    Integrable.of_bound (hf.abs.pow_const j).aestronglyMeasurable (B ^ j)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB x) j)
  have ev : ∀ x (m : ℕ), |f x| ^ (2 * m) = f x ^ (2 * m) := fun x m => pow_abs_two_mul _
  have e2 : (fun x => f x ^ 2) = fun x => |f x| ^ 2 := funext fun x => (ev x 1).symm
  have e4 : (fun x => f x ^ 4) = fun x => |f x| ^ 4 := funext fun x => (ev x 2).symm
  have e6 : (fun x => f x ^ 6) = fun x => |f x| ^ 6 := funext fun x => (ev x 3).symm
  rw [e2, e4, e6]
  constructor
  · have h := BstLean.Part138.cs_sq μ (f := fun x => |f x|) (g := fun x => |f x| ^ 2)
      (ia 2) (by simpa only [← pow_mul] using ia 4)
      (by simpa only [show ∀ x, |f x| * |f x| ^ 2 = |f x| ^ 3 from fun x => by ring] using ia 3)
    simpa only [show ∀ x, |f x| * |f x| ^ 2 = |f x| ^ 3 from fun x => by ring, ← pow_mul] using h
  · have h := BstLean.Part138.cs_sq μ (f := fun x => |f x| ^ 2) (g := fun x => |f x| ^ 3)
      (by simpa only [← pow_mul] using ia 4) (by simpa only [← pow_mul] using ia 6)
      (by simpa only [show ∀ x, |f x| ^ 2 * |f x| ^ 3 = |f x| ^ 5 from fun x => by ring] using ia 5)
    simpa only [show ∀ x, |f x| ^ 2 * |f x| ^ 3 = |f x| ^ 5 from fun x => by ring, ← pow_mul]
      using h

/-- The expectation of the first-order part `L` of `T` for CENTRED parameters:
`E L ≤ κ[n v_ε²/4 + a²(1 + ε₀) v_δ v_ε]`. -/
lemma EL_bound {V : Type*} [MeasurableSpace V] (pm : Measure V) [IsProbabilityMeasure pm]
    (n : ℕ) {a2 ε₀ δ₀ : ℝ} {δ ε : V → ℝ} (hδm : Measurable δ) (hεm : Measurable ε)
    (ha : 0 ≤ a2) (hε₀ : ε₀ < 1) (hwε : ∀ v, |ε v| ≤ ε₀) (hwδ : ∀ v, |δ v| ≤ δ₀)
    (hmδ : ∫ v, δ v ∂pm = 0) (hmε : ∫ v, ε v ∂pm = 0) :
    ∫ w, (n / 2 * (ε w.1 * ε w.2) + n * (1 - ε₀ ^ 2)⁻¹ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) +
        a2 * (δ w.1 * δ w.2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) +
        a2 / 2 * (δ w.1 ^ 2 * ε w.2) + a2 / 2 * (ε w.1 * δ w.2 ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|))) ∂(pm.prod pm) ≤
      (1 - ε₀ ^ 2)⁻¹ * (n * (∫ v, ε v ^ 2 ∂pm) ^ 2 / 4 +
        a2 * (1 + ε₀) * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ^ 2 ∂pm)) ∧
    Integrable (fun w : V × V => n / 2 * (ε w.1 * ε w.2) +
        n * (1 - ε₀ ^ 2)⁻¹ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 * (δ w.1 * δ w.2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) +
        a2 / 2 * (δ w.1 ^ 2 * ε w.2) + a2 / 2 * (ε w.1 * δ w.2 ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|))) (pm.prod pm) := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwε (Classical.arbitrary V))
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwδ (Classical.arbitrary V))
  have hd0 : 0 < 1 - ε₀ ^ 2 := by nlinarith
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have hκ0 : 0 < κ := inv_pos.mpr hd0
  have ibd : ∀ {f : V → ℝ}, Measurable f → ∀ M : ℝ, (∀ v, |f v| ≤ M) → Integrable f pm :=
    fun {f} hf M hM => Integrable.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun v => by rw [Real.norm_eq_abs]; exact hM v)
  have bε2 : ∀ v, ε v ^ 2 ≤ ε₀ ^ 2 := fun v => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hwε v) 2
  have bδ2 : ∀ v, δ v ^ 2 ≤ δ₀ ^ 2 := fun v => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hwδ v) 2
  have iε := ibd hεm ε₀ hwε
  have iε2 := ibd (hεm.pow_const 2) (ε₀ ^ 2) fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact bε2 v
  have iδ := ibd hδm δ₀ hwδ
  have iδ2 := ibd (hδm.pow_const 2) (δ₀ ^ 2) fun v => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact bδ2 v
  have iδε := ibd (hδm.abs.mul hεm.abs) (δ₀ * ε₀) fun v => by
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact mul_le_mul (hwδ v) (hwε v) (abs_nonneg _) hδ0
  have iδ2ε := ibd ((hδm.pow_const 2).mul hεm.abs) (δ₀ ^ 2 * ε₀) fun v => by
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _))]
    exact mul_le_mul (bδ2 v) (hwε v) (abs_nonneg _) (sq_nonneg _)
  have i1 := iε.mul_prod iε
  have i2 := iε2.mul_prod iε2
  have i3 := iδ.mul_prod iδ
  have i4 := iδε.mul_prod iδε
  have i5 := iδ2.mul_prod iε
  have i6 := iε.mul_prod iδ2
  have i7 := iδ2ε.mul_prod iε2
  have i8 := iε2.mul_prod iδ2ε
  refine ⟨?_, by fun_prop⟩
  repeat rw [integral_add]
  all_goals try fun_prop
  simp only [integral_const_mul]
  rw [integral_prod_mul ε ε, integral_prod_mul (fun v => ε v ^ 2) (fun v => ε v ^ 2),
    integral_prod_mul δ δ, integral_prod_mul (fun v => |δ v| * |ε v|) (fun v => |δ v| * |ε v|),
    integral_prod_mul (fun v => δ v ^ 2) ε, integral_prod_mul ε (fun v => δ v ^ 2),
    integral_prod_mul (fun v => δ v ^ 2 * |ε v|) (fun v => ε v ^ 2),
    integral_prod_mul (fun v => ε v ^ 2) (fun v => δ v ^ 2 * |ε v|), hmδ, hmε]
  set vε := ∫ v, ε v ^ 2 ∂pm
  set vδ := ∫ v, δ v ^ 2 ∂pm
  set X := ∫ v, |δ v| * |ε v| ∂pm
  set Y := ∫ v, δ v ^ 2 * |ε v| ∂pm
  have hvε : 0 ≤ vε := integral_nonneg fun v => sq_nonneg _
  have hX : X ^ 2 ≤ vδ * vε := by
    have h := BstLean.Part138.cs_sq pm (f := fun v => |δ v|) (g := fun v => |ε v|)
      (by simpa only [sq_abs] using iδ2) (by simpa only [sq_abs] using iε2) iδε
    simpa only [sq_abs] using h
  have hY : Y ≤ ε₀ * vδ := by
    have h := integral_mono iδ2ε (iδ2.const_mul ε₀) (fun v => by
      change δ v ^ 2 * |ε v| ≤ ε₀ * δ v ^ 2
      nlinarith [hwε v, sq_nonneg (δ v)])
    rwa [integral_const_mul] at h
  have f1 : a2 * κ * (X * X) ≤ a2 * κ * (vδ * vε) :=
    mul_le_mul_of_nonneg_left (by rw [← sq]; exact hX) (mul_nonneg ha hκ0.le)
  have f2 : a2 * κ / 2 * (Y * vε) ≤ a2 * κ / 2 * (ε₀ * vδ * vε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY hvε)
      (div_nonneg (mul_nonneg ha hκ0.le) (by norm_num))
  clear_value vε vδ X Y κ
  linear_combination f1 + 2 * f2

section six

variable {V : Type*} [MeasurableSpace V]

/-- The `k`-th absolute moment norm `‖f‖_k = (E |f|^k)^{1/k}`. -/
noncomputable def momN (pm : Measure V) (k : ℕ) (f : V → ℝ) : ℝ :=
  (∫ v, |f v| ^ k ∂pm) ^ ((k : ℝ)⁻¹)

lemma momN_nonneg (pm : Measure V) (k : ℕ) (f : V → ℝ) : 0 ≤ momN pm k f :=
  Real.rpow_nonneg (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _) _

lemma momN_pow (pm : Measure V) {k : ℕ} (hk : k ≠ 0) (f : V → ℝ) :
    momN pm k f ^ k = ∫ v, |f v| ^ k ∂pm :=
  Real.rpow_inv_natCast_pow (integral_nonneg fun v => pow_nonneg (abs_nonneg _) _) hk

/-- **The paper's `𝒯_k = κ[(n/2)‖ε‖_k² + a²‖δ‖_k² + a² δ₀ ‖δ‖_k ‖ε‖_k]`.** -/
noncomputable def bigT (pm : Measure V) (k n : ℕ) (a2 κ δ₀ : ℝ) (δ ε : V → ℝ) : ℝ :=
  κ * (n / 2 * momN pm k ε ^ 2 + a2 * momN pm k δ ^ 2 + a2 * δ₀ * momN pm k δ * momN pm k ε)

/-- `E_{pm⊗pm} (c |f(v)| |g(v')|)^k = (c ‖f‖_k ‖g‖_k)^k`. -/
lemma prod_moment (pm : Measure V) [IsProbabilityMeasure pm] {k : ℕ} (hk : k ≠ 0) {c : ℝ}
    (hc : 0 ≤ c) (f g : V → ℝ) :
    ∫ w, (c * (|f w.1| * |g w.2|)) ^ k ∂(pm.prod pm) =
      (c * momN pm k f * momN pm k g) ^ k := by
  have e : (fun w : V × V => (c * (|f w.1| * |g w.2|)) ^ k) =
      fun w => c ^ k * (|f w.1| ^ k * |g w.2| ^ k) := by
    funext w; ring
  rw [e, integral_const_mul, integral_prod_mul (fun v => |f v| ^ k) (fun v => |g v| ^ k),
    mul_pow, mul_pow, momN_pow pm hk, momN_pow pm hk]
  ring

/-- **The centred sixth-order bound (formula `t7:p07:chi-six`).** `pm` is a probability measure
on the parameters; `δ`, `ε` are measurable, CENTRED (`E δ = E ε = 0`), with `|ε| ≤ ε₀ < 1`,
`|δ| ≤ δ₀`; `a² ≥ 0`; `κ = 1/(1 − ε₀²)`, `T_max = κ(n ε₀²/2 + a² δ₀²(1 + ε₀))`. Then
`E_{pm⊗pm} kTwo − 1 ≤ κ[n v_ε²/4 + a²(1 + ε₀) v_δ v_ε] + 𝒯₂²/2 + 𝒯₂𝒯₄²/6 + 𝒯₄⁴/24 +
𝒯₄²𝒯₆³/120 + e^{T_max} 𝒯₆⁶/720`. (The paper has `𝒯₆⁵/120` in place of `𝒯₄²𝒯₆³/120`; the Lean
term is not larger, because `‖·‖₄ ≤ ‖·‖₆` on a probability space.) -/
theorem chi_six (pm : Measure V) [IsProbabilityMeasure pm] (n : ℕ) {a2 ε₀ δ₀ : ℝ}
    {δ ε : V → ℝ} (hδm : Measurable δ) (hεm : Measurable ε) (ha : 0 ≤ a2) (hε₀ : ε₀ < 1)
    (hwε : ∀ v, |ε v| ≤ ε₀) (hwδ : ∀ v, |δ v| ≤ δ₀) (hmδ : ∫ v, δ v ∂pm = 0)
    (hmε : ∫ v, ε v ∂pm = 0) :
    ∫ w, kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) ∂(pm.prod pm) - 1 ≤
      (1 - ε₀ ^ 2)⁻¹ * (n * (∫ v, ε v ^ 2 ∂pm) ^ 2 / 4 +
          a2 * (1 + ε₀) * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ^ 2 ∂pm)) +
        bigT pm 2 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 2 / 2 +
        bigT pm 2 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε * bigT pm 4 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 2 / 6 +
        bigT pm 4 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 4 / 24 +
        bigT pm 4 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 2 * bigT pm 6 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 3 / 120 +
        exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀))) *
          bigT pm 6 n a2 (1 - ε₀ ^ 2)⁻¹ δ₀ δ ε ^ 6 / 720 := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwε (Classical.arbitrary V))
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwδ (Classical.arbitrary V))
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have hd0 : 0 < 1 - ε₀ ^ 2 := by nlinarith
  have hκ0 : 0 < κ := inv_pos.mpr hd0
  set Tm := κ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀)) with hTm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the function `T = log kTwo` and its pieces
  set K : V × V → ℝ := fun w => kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) with hK
  set T : V × V → ℝ := fun w => log (K w) with hT
  have mK : Measurable K :=
    (measurable_kTwo n).comp (measurable_const.prodMk
      (((hδm.comp measurable_fst).prodMk (hεm.comp measurable_fst)).prodMk
        ((hδm.comp measurable_snd).prodMk (hεm.comp measurable_snd))))
  have mT : Measurable T := mK.log
  have hKpos : ∀ w, 0 < K w := fun w => by
    simp only [hK, kTwo]
    have h1 := hwε w.1
    have h2 := hwε w.2
    have : |ε w.1 * ε w.2| ≤ ε₀ ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hε0
    have hD : 0 < 1 - ε w.1 * ε w.2 := by linarith [(abs_le.mp this).2]
    exact mul_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr hD)) n) (exp_pos _)
  have hKT : ∀ w, K w = exp (T w) := fun w => (Real.exp_log (hKpos w)).symm
  set c1 := κ * (n / 2) with hc1
  set c2 := κ * a2 with hc2
  set c3 := κ * (a2 / 2 * δ₀) with hc3
  have c1n : 0 ≤ c1 := by positivity
  have c2n : 0 ≤ c2 := by positivity
  have c3n : 0 ≤ c3 := by positivity
  set g1 : V × V → ℝ := fun w => c1 * (|ε w.1| * |ε w.2|) with hg1
  set g2 : V × V → ℝ := fun w => c2 * (|δ w.1| * |δ w.2|) with hg2
  set g3 : V × V → ℝ := fun w => c3 * (|δ w.1| * |ε w.2|) with hg3
  set g4 : V × V → ℝ := fun w => c3 * (|ε w.1| * |δ w.2|) with hg4
  have hTg : ∀ w, |T w| ≤ g1 w + g2 w + g3 w + g4 w := fun w =>
    (T_parts n ha hε₀ (hwε w.1) (hwε w.2) (hwδ w.1) (hwδ w.2)).2
  have hTL : ∀ w, T w ≤
      n / 2 * (ε w.1 * ε w.2) + n * κ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 * (δ w.1 * δ w.2) +
        a2 * κ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) + a2 / 2 * (δ w.1 ^ 2 * ε w.2) +
        a2 / 2 * (ε w.1 * δ w.2 ^ 2) + a2 * κ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
        a2 * κ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|)) := fun w =>
    (T_parts n ha hε₀ (hwε w.1) (hwε w.2) (hwδ w.1) (hwδ w.2)).1
  -- bounds of the pieces
  have pe : ∀ v, |ε v| * |ε v| ≤ ε₀ * ε₀ := fun v =>
    mul_le_mul (hwε v) (hwε v) (abs_nonneg _) hε0
  have pd : ∀ v, |δ v| * |δ v| ≤ δ₀ * δ₀ := fun v =>
    mul_le_mul (hwδ v) (hwδ v) (abs_nonneg _) hδ0
  set M := c1 * (ε₀ * ε₀) + c2 * (δ₀ * δ₀) + c3 * (δ₀ * ε₀) + c3 * (ε₀ * δ₀) with hM
  have g1n : ∀ w, 0 ≤ g1 w := fun w => mul_nonneg c1n (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have g2n : ∀ w, 0 ≤ g2 w := fun w => mul_nonneg c2n (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have g3n : ∀ w, 0 ≤ g3 w := fun w => mul_nonneg c3n (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have g4n : ∀ w, 0 ≤ g4 w := fun w => mul_nonneg c3n (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have g1b : ∀ w, g1 w ≤ c1 * (ε₀ * ε₀) := fun w =>
    mul_le_mul_of_nonneg_left (mul_le_mul (hwε _) (hwε _) (abs_nonneg _) hε0) c1n
  have g2b : ∀ w, g2 w ≤ c2 * (δ₀ * δ₀) := fun w =>
    mul_le_mul_of_nonneg_left (mul_le_mul (hwδ _) (hwδ _) (abs_nonneg _) hδ0) c2n
  have g3b : ∀ w, g3 w ≤ c3 * (δ₀ * ε₀) := fun w =>
    mul_le_mul_of_nonneg_left (mul_le_mul (hwδ _) (hwε _) (abs_nonneg _) hδ0) c3n
  have g4b : ∀ w, g4 w ≤ c3 * (ε₀ * δ₀) := fun w =>
    mul_le_mul_of_nonneg_left (mul_le_mul (hwε _) (hwδ _) (abs_nonneg _) hε0) c3n
  have g1M : ∀ w, g1 w ≤ M := fun w => by
    have := g1b w; have : 0 ≤ c2 * (δ₀ * δ₀) := by positivity
    have : 0 ≤ c3 * (δ₀ * ε₀) := by positivity
    linarith
  have g2M : ∀ w, g2 w ≤ M := fun w => by
    have := g2b w; have : 0 ≤ c1 * (ε₀ * ε₀) := by positivity
    have : 0 ≤ c3 * (δ₀ * ε₀) := by positivity
    linarith
  have g3M : ∀ w, g3 w ≤ M := fun w => by
    have := g3b w; have : 0 ≤ c1 * (ε₀ * ε₀) := by positivity
    have : 0 ≤ c2 * (δ₀ * δ₀) := by positivity
    have : 0 ≤ c3 * (ε₀ * δ₀) := by positivity
    linarith [hM]
  have g4M : ∀ w, g4 w ≤ M := fun w => by
    have := g4b w; have : 0 ≤ c1 * (ε₀ * ε₀) := by positivity
    have : 0 ≤ c2 * (δ₀ * δ₀) := by positivity
    have : 0 ≤ c3 * (δ₀ * ε₀) := by positivity
    linarith
  have hMT : M = Tm := by
    rw [hM, hTm, hc1, hc2, hc3]; ring
  have hTabs : ∀ w, |T w| ≤ Tm := fun w => by
    have := hTg w
    linarith [g1b w, g2b w, g3b w, g4b w, hM, hMT]
  have mg1 : Measurable g1 := measurable_const.mul
    ((hεm.comp measurable_fst).abs.mul (hεm.comp measurable_snd).abs)
  have mg2 : Measurable g2 := measurable_const.mul
    ((hδm.comp measurable_fst).abs.mul (hδm.comp measurable_snd).abs)
  have mg3 : Measurable g3 := measurable_const.mul
    ((hδm.comp measurable_fst).abs.mul (hεm.comp measurable_snd).abs)
  have mg4 : Measurable g4 := measurable_const.mul
    ((hεm.comp measurable_fst).abs.mul (hδm.comp measurable_snd).abs)
  -- `E (Σ g)^k ≤ 𝒯_k^k`
  have hmk : ∀ k : ℕ, k ≠ 0 →
      ∫ w, (g1 w + g2 w + g3 w + g4 w) ^ k ∂(pm.prod pm) ≤ bigT pm k n a2 κ δ₀ δ ε ^ k := by
    intro k hk
    have e : bigT pm k n a2 κ δ₀ δ ε = c1 * momN pm k ε * momN pm k ε +
        c2 * momN pm k δ * momN pm k δ + c3 * momN pm k δ * momN pm k ε +
        c3 * momN pm k ε * momN pm k δ := by
      unfold bigT; rw [hc1, hc2, hc3]; ring
    rw [e]
    have nn := momN_nonneg pm k
    exact mink4 (pm.prod pm) k mg1 mg2 mg3 mg4 g1n g2n g3n g4n g1M g2M g3M g4M
      (mul_nonneg (mul_nonneg c1n (nn ε)) (nn ε)) (mul_nonneg (mul_nonneg c2n (nn δ)) (nn δ))
      (mul_nonneg (mul_nonneg c3n (nn δ)) (nn ε)) (mul_nonneg (mul_nonneg c3n (nn ε)) (nn δ))
      (le_of_eq (prod_moment pm hk c1n ε ε)) (le_of_eq (prod_moment pm hk c2n δ δ))
      (le_of_eq (prod_moment pm hk c3n δ ε)) (le_of_eq (prod_moment pm hk c3n ε δ))
  clear_value T K g1 g2 g3 g4
  -- integrability of the powers of `T`
  have iTp : ∀ j : ℕ, Integrable (fun w => T w ^ j) (pm.prod pm) := fun j =>
    Integrable.of_bound (mT.pow_const j).aestronglyMeasurable (Tm ^ j)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hTabs w) j)
  have iTa : ∀ j : ℕ, Integrable (fun w => |T w| ^ j) (pm.prod pm) := fun j =>
    Integrable.of_bound (mT.abs.pow_const j).aestronglyMeasurable (Tm ^ j)
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hTabs w) j)
  have iG : ∀ k : ℕ, Integrable (fun w => (g1 w + g2 w + g3 w + g4 w) ^ k) (pm.prod pm) :=
    fun k => Integrable.of_bound ((((mg1.add mg2).add mg3).add mg4).pow_const k).aestronglyMeasurable
      ((4 * M) ^ k) (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ k
        rw [abs_of_nonneg (by linarith [g1n w, g2n w, g3n w, g4n w])]
        linarith [g1M w, g2M w, g3M w, g4M w])
  have hEven : ∀ m : ℕ, m ≠ 0 → ∫ w, T w ^ (2 * m) ∂(pm.prod pm) ≤
      bigT pm (2 * m) n a2 κ δ₀ δ ε ^ (2 * m) := by
    intro m hm
    refine le_trans (integral_mono (iTp _) (iG _) fun w => ?_) (hmk (2 * m) (by omega))
    change T w ^ (2 * m) ≤ (g1 w + g2 w + g3 w + g4 w) ^ (2 * m)
    rw [← pow_abs_two_mul]
    exact pow_le_pow_left₀ (abs_nonneg _) (hTg w) _
  set T2 := bigT pm 2 n a2 κ δ₀ δ ε with hT2d
  set T4 := bigT pm 4 n a2 κ δ₀ δ ε with hT4d
  set T6 := bigT pm 6 n a2 κ δ₀ δ ε with hT6d
  have hT2n : 0 ≤ T2 := by
    rw [hT2d]; unfold bigT
    have := momN_nonneg pm 2 δ; have := momN_nonneg pm 2 ε; positivity
  have hT4n : 0 ≤ T4 := by
    rw [hT4d]; unfold bigT
    have := momN_nonneg pm 4 δ; have := momN_nonneg pm 4 ε; positivity
  have hT6n : 0 ≤ T6 := by
    rw [hT6d]; unfold bigT
    have := momN_nonneg pm 6 δ; have := momN_nonneg pm 6 ε; positivity
  have E2 : ∫ w, T w ^ 2 ∂(pm.prod pm) ≤ T2 ^ 2 := by
    have h := hEven 1 one_ne_zero; rw [hT2d]; simpa using h
  have E4 : ∫ w, T w ^ 4 ∂(pm.prod pm) ≤ T4 ^ 4 := by
    have h := hEven 2 two_ne_zero; rw [hT4d]; simpa using h
  have E6 : ∫ w, T w ^ 6 ∂(pm.prod pm) ≤ T6 ^ 6 := by
    have h := hEven 3 three_ne_zero; rw [hT6d]; simpa using h
  have E2n : 0 ≤ ∫ w, T w ^ 2 ∂(pm.prod pm) := integral_nonneg fun w => sq_nonneg _
  have E4n : 0 ≤ ∫ w, T w ^ 4 ∂(pm.prod pm) :=
    integral_nonneg fun w => by positivity
  -- `E|T|³ ≤ 𝒯₂𝒯₄²` and `E|T|⁵ ≤ 𝒯₄²𝒯₆³`
  obtain ⟨cs3, cs5⟩ := cs_odd (pm.prod pm) mT hTabs
  have E6n : 0 ≤ ∫ w, T w ^ 6 ∂(pm.prod pm) := integral_nonneg fun w => by positivity
  have E3 : ∫ w, |T w| ^ 3 ∂(pm.prod pm) ≤ T2 * T4 ^ 2 := by
    have hn : 0 ≤ ∫ w, |T w| ^ 3 ∂(pm.prod pm) := integral_nonneg fun w => by positivity
    have h2 : (∫ w, |T w| ^ 3 ∂(pm.prod pm)) ^ 2 ≤ (T2 * T4 ^ 2) ^ 2 := by
      refine cs3.trans ?_
      have := mul_le_mul E2 E4 E4n (sq_nonneg _)
      linarith [show (T2 * T4 ^ 2) ^ 2 = T2 ^ 2 * T4 ^ 4 by ring]
    exact (pow_le_pow_iff_left₀ hn (by positivity) two_ne_zero).mp h2
  have E5 : ∫ w, |T w| ^ 5 ∂(pm.prod pm) ≤ T4 ^ 2 * T6 ^ 3 := by
    have hn : 0 ≤ ∫ w, |T w| ^ 5 ∂(pm.prod pm) := integral_nonneg fun w => by positivity
    have h2 : (∫ w, |T w| ^ 5 ∂(pm.prod pm)) ^ 2 ≤ (T4 ^ 2 * T6 ^ 3) ^ 2 := by
      refine cs5.trans ?_
      have := mul_le_mul E4 E6 E6n (by positivity)
      linarith [show (T4 ^ 2 * T6 ^ 3) ^ 2 = T4 ^ 4 * T6 ^ 6 by ring]
    exact (pow_le_pow_iff_left₀ hn (by positivity) two_ne_zero).mp h2
  -- `E T`
  obtain ⟨hEL, iL⟩ := EL_bound pm n hδm hεm ha hε₀ hwε hwδ hmδ hmε
  have ET : ∫ w, T w ∂(pm.prod pm) ≤ κ * (n * (∫ v, ε v ^ 2 ∂pm) ^ 2 / 4 +
      a2 * (1 + ε₀) * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ^ 2 ∂pm)) :=
    (integral_mono (by simpa using iTp 1) iL hTL).trans hEL
  -- the pointwise sixth-order bound
  have hpt : ∀ w, K w - 1 ≤ T w + T w ^ 2 / 2 + |T w| ^ 3 / 6 + T w ^ 4 / 24 + |T w| ^ 5 / 120 +
      exp Tm * T w ^ 6 / 720 := fun w => by
    rw [hKT w]
    have h6 := exp_le_six (T w)
    have h3 : T w ^ 3 ≤ |T w| ^ 3 := by rw [← abs_pow]; exact le_abs_self _
    have h5 : T w ^ 5 ≤ |T w| ^ 5 := by rw [← abs_pow]; exact le_abs_self _
    have hm : exp (max (T w) 0) * T w ^ 6 ≤ exp Tm * T w ^ 6 :=
      mul_le_mul_of_nonneg_right (exp_le_exp.mpr (max_le ((le_abs_self _).trans (hTabs w))
        ((abs_nonneg _).trans (hTabs w)))) (by positivity)
    linarith
  have iK : Integrable K (pm.prod pm) :=
    Integrable.of_bound mK.aestronglyMeasurable (exp Tm) (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_pos (hKpos w), hKT w]
      exact exp_le_exp.mpr ((le_abs_self _).trans (hTabs w)))
  have iR : Integrable (fun w => T w + T w ^ 2 / 2 + |T w| ^ 3 / 6 + T w ^ 4 / 24 +
      |T w| ^ 5 / 120 + exp Tm * T w ^ 6 / 720) (pm.prod pm) := by
    have h1 := iTp 1
    simp only [pow_one] at h1
    exact (((((h1.add ((iTp 2).div_const _)).add ((iTa 3).div_const _)).add
      ((iTp 4).div_const _)).add ((iTa 5).div_const _)).add (((iTp 6).const_mul _).div_const _))
  have hI := integral_mono (f := fun w => K w - 1) (iK.sub (integrable_const (1 : ℝ))) iR hpt
  have hsplit : ∫ w, (T w + T w ^ 2 / 2 + |T w| ^ 3 / 6 + T w ^ 4 / 24 + |T w| ^ 5 / 120 +
      exp Tm * T w ^ 6 / 720) ∂(pm.prod pm) = ∫ w, T w ∂(pm.prod pm) +
      (∫ w, T w ^ 2 ∂(pm.prod pm)) / 2 + (∫ w, |T w| ^ 3 ∂(pm.prod pm)) / 6 +
      (∫ w, T w ^ 4 ∂(pm.prod pm)) / 24 + (∫ w, |T w| ^ 5 ∂(pm.prod pm)) / 120 +
      exp Tm * (∫ w, T w ^ 6 ∂(pm.prod pm)) / 720 := by
    have h1 := iTp 1
    simp only [pow_one] at h1
    repeat rw [integral_add]
    all_goals first
      | exact h1
      | exact (iTp 2).div_const _
      | exact (iTa 3).div_const _
      | exact (iTp 4).div_const _
      | exact (iTa 5).div_const _
      | exact ((iTp 6).const_mul _).div_const _
      | skip
    · simp only [integral_div, integral_const_mul]
    all_goals first
      | exact h1.add ((iTp 2).div_const _)
      | exact (h1.add ((iTp 2).div_const _)).add ((iTa 3).div_const _)
      | exact ((h1.add ((iTp 2).div_const _)).add ((iTa 3).div_const _)).add
          ((iTp 4).div_const _)
      | exact (((h1.add ((iTp 2).div_const _)).add ((iTa 3).div_const _)).add
          ((iTp 4).div_const _)).add ((iTa 5).div_const _)
  rw [hsplit, integral_sub iK (integrable_const 1)] at hI
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hI
  have hTm0 : 0 ≤ exp Tm := (exp_pos _).le
  have := mul_le_mul_of_nonneg_left E6 hTm0
  change ∫ w, K w ∂(pm.prod pm) - 1 ≤ _
  linarith

end six

end BstLean.Part161

open BstLean.Part161 in
#print axioms exp_le_six
open BstLean.Part161 in
#print axioms T_parts
open BstLean.Part161 in
#print axioms mink4
open BstLean.Part161 in
#print axioms chi_six
