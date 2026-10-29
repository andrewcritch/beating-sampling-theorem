import BstLean.Part161Chi

/-!
# Part 161, item 1(c): the second-order bound of the chi-square in a uniform window

Role: `delegations/statements/p161-spec.md`, item 1(c) (the corollary). Do not use `sorry`,
`native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Corollary `t7:p07:chi-bounds`, the
"general conclusion" (marked "for comparison only, unused" in the paper; the assembly uses the
sixth-order centred form `t7:p07:chi-six`, which is NOT in Lean).

* `neg_log_le`, `le_neg_log`, `abs_log_le`: `w ≤ −log(1 − w) ≤ w + w²/(2(1 − r))` and
  `|log(1 − w)| ≤ |w|/(1 − r)` for `|w| ≤ r < 1`.
* `exp_le_quad`: `e^T ≤ 1 + T + e^{max(T, 0)} T²/2`.
* `kTwo_eq_exp`: `kTwo = e^T` with the paper's `T`.
* `kTwo_pt`: the pointwise second-order bound `kTwo − 1 ≤ L + e^{T_max}/2·Q`.
* **`chi_general`**: `E_{π⊗π} kTwo − 1 ≤ (n/2) m_ε² + a² m_δ² + a² v_δ m_ε +
  κ[n v_ε²/4 + a²(1 + ε₀) v_δ v_ε] + 2κ² e^{T_max}[n² v_ε²/4 + a⁴ v_δ² + (a⁴/2) δ₀² v_δ v_ε]`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open scoped Nat

/-- `w ≤ −log(1 − w)` for `w < 1`. -/
lemma le_neg_log {w : ℝ} (hw : w < 1) : w ≤ -log (1 - w) := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - w)
  linarith

/-- `−log(1 − w) ≤ w + w²/(2(1 − r))` for `|w| ≤ r < 1`. -/
lemma neg_log_le {w r : ℝ} (hw : |w| ≤ r) (hr : r < 1) :
    -log (1 - w) ≤ w + w ^ 2 / (2 * (1 - r)) := by
  have hw1 : |w| < 1 := lt_of_le_of_lt hw hr
  have hS := Real.hasSum_pow_div_log_of_abs_lt_one hw1
  have hT := (hasSum_nat_add_iff' (f := fun n : ℕ => w ^ (n + 1) / (n + 1)) 1).mpr hS
  simp only [Finset.range_one, Finset.sum_singleton, zero_add, pow_one, Nat.cast_zero,
    div_one] at hT
  have ha0 : 0 ≤ |w| := abs_nonneg w
  have hG := (hasSum_geometric_of_lt_one ha0 hw1).mul_left (w ^ 2 / 2)
  have hle : ∀ k : ℕ, w ^ (k + 1 + 1) / ((k + 1 : ℕ) + 1 : ℝ) ≤ w ^ 2 / 2 * |w| ^ k := by
    intro k
    have h1 : w ^ (k + 1 + 1) ≤ |w| ^ (k + 1 + 1) := by
      rw [← abs_pow]; exact le_abs_self _
    have h2 : |w| ^ (k + 1 + 1) = w ^ 2 * |w| ^ k := by
      rw [show k + 1 + 1 = 2 + k by ring, pow_add, sq_abs]
    have h3 : (2 : ℝ) ≤ ((k + 1 : ℕ) + 1 : ℝ) := by push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have h4 : 0 ≤ |w| ^ (k + 1 + 1) := pow_nonneg ha0 _
    calc w ^ (k + 1 + 1) / ((k + 1 : ℕ) + 1 : ℝ) ≤ |w| ^ (k + 1 + 1) / ((k + 1 : ℕ) + 1 : ℝ) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ |w| ^ (k + 1 + 1) / 2 := div_le_div_of_nonneg_left h4 (by norm_num) h3
      _ = w ^ 2 / 2 * |w| ^ k := by rw [h2]; ring
  have hsum := hasSum_le hle hT hG
  have hgeo : w ^ 2 / 2 * (1 - |w|)⁻¹ ≤ w ^ 2 / (2 * (1 - r)) := by
    rw [div_mul_eq_mul_div, ← div_eq_mul_inv]
    have : 0 < 1 - r := by linarith
    have : 0 < 1 - |w| := by linarith
    rw [div_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (by nlinarith)
  linarith

/-- `|log(1 − w)| ≤ |w|/(1 − r)` for `|w| ≤ r < 1`. -/
lemma abs_log_le {w r : ℝ} (hw : |w| ≤ r) (hr : r < 1) : |log (1 - w)| ≤ |w| / (1 - r) := by
  have hw1 : w < 1 := lt_of_le_of_lt (le_abs_self w) (lt_of_le_of_lt hw hr)
  have hr0 : 0 < 1 - r := by linarith
  have hpos : 0 < 1 - w := by linarith
  have h1 := le_neg_log hw1
  have h2 : -log (1 - w) ≤ w / (1 - w) := by
    have := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at this
    have e : (1 - w)⁻¹ - 1 = w / (1 - w) := by field_simp; ring
    linarith
  have h3 : w / (1 - w) ≤ |w| / (1 - r) := by
    have hle : 1 - r ≤ 1 - w := by linarith [le_abs_self w]
    calc w / (1 - w) ≤ |w| / (1 - w) := div_le_div_of_nonneg_right (le_abs_self w) hpos.le
      _ ≤ |w| / (1 - r) := div_le_div_of_nonneg_left (abs_nonneg w) hr0 hle
  have h4 : |w| ≤ |w| / (1 - r) := by
    rw [le_div_iff₀ hr0]; nlinarith [abs_nonneg w]
  rw [abs_le]
  constructor
  · linarith
  · linarith [neg_abs_le w]

/-- **The second-order exponential bound** `e^T ≤ 1 + T + e^{max(T, 0)}·T²/2`. -/
lemma exp_le_quad (T : ℝ) : exp T ≤ 1 + T + exp (max T 0) * T ^ 2 / 2 := by
  rcases le_total 0 T with hT | hT
  · rw [max_eq_left hT]
    have hS := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) T
    rw [← Real.exp_eq_exp_ℝ] at hS
    have hT2 := (hasSum_nat_add_iff' (f := fun n : ℕ => T ^ n / (n ! : ℝ)) 2).mpr hS
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, zero_add, pow_one, Nat.factorial_one] at hT2
    have hG := hS.mul_left (T ^ 2 / 2)
    have hle : ∀ k : ℕ, T ^ (k + 2) / ((k + 2)! : ℝ) ≤ T ^ 2 / 2 * (T ^ k / (k ! : ℝ)) := by
      intro k
      have hf : (2 : ℝ) * (k ! : ℝ) ≤ ((k + 2)! : ℝ) := by
        have : 2 * k ! ≤ (k + 2)! := by
          rw [Nat.factorial_succ, Nat.factorial_succ, ← mul_assoc]
          have h2 : 2 ≤ (k + 1 + 1) * (k + 1) := by nlinarith
          exact Nat.mul_le_mul_right _ h2
        exact_mod_cast this
      have hk : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hpow : 0 ≤ T ^ (k + 2) := pow_nonneg hT _
      rw [show T ^ 2 / 2 * (T ^ k / (k ! : ℝ)) = T ^ (k + 2) / (2 * (k ! : ℝ)) by
        rw [pow_add]; field_simp]
      exact div_le_div_of_nonneg_left hpow (by positivity) hf
    have hsum := hasSum_le hle hT2 hG
    norm_num at hsum
    nlinarith
  · rw [max_eq_right hT, exp_zero, one_mul]
    set x := -T with hx
    have hx0 : 0 ≤ x := by rw [hx]; linarith
    have hE := Real.sum_le_exp_of_nonneg hx0 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
      Nat.factorial, Nat.cast_one, div_one, zero_add, pow_one] at hE
    norm_num at hE
    have hq : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
    have hmul : 1 ≤ exp x * (1 - x + x ^ 2 / 2) := by
      have h1 : (1 + x + x ^ 2 / 2 + x ^ 3 / 6) * (1 - x + x ^ 2 / 2) ≤
          exp x * (1 - x + x ^ 2 / 2) := mul_le_mul_of_nonneg_right (by linarith) hq.le
      nlinarith [pow_nonneg hx0 3, pow_nonneg hx0 4, pow_nonneg hx0 5]
    have he : exp T = (exp x)⁻¹ := by rw [hx, Real.exp_neg, inv_inv]
    rw [he]
    have hex : 0 < exp x := exp_pos x
    rw [inv_le_iff_one_le_mul₀ hex]
    have : 1 + T + T ^ 2 / 2 = 1 - x + x ^ 2 / 2 := by rw [hx]; ring
    rw [this]
    linarith

lemma sq4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- **`kTwo = e^T`** with `T = −(n/2) log(1 − εε') + a²(2δδ' + δ²ε' + δ'²ε)/(2(1 − εε'))`. -/
lemma kTwo_eq_exp (n : ℕ) (a2 δ ε δ' ε' : ℝ) (hD : 0 < 1 - ε * ε') :
    kTwo n a2 δ ε δ' ε' = exp (-(n / 2) * log (1 - ε * ε') +
      a2 * (2 * δ * δ' + δ ^ 2 * ε' + δ' ^ 2 * ε) / (2 * (1 - ε * ε'))) := by
  unfold kTwo
  rw [Real.exp_add]
  congr 1
  have hs : 0 < (√(1 - ε * ε'))⁻¹ ^ n := pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr hD)) n
  rw [← Real.exp_log hs, Real.log_pow, Real.log_inv, Real.log_sqrt hD.le]
  congr 1
  ring

/-- **The pointwise second-order bound of the two-copy kernel** in the window
`|ε|, |ε'| ≤ ε₀ < 1`, `|δ|, |δ'| ≤ δ₀`, `a² ≥ 0`; `κ = 1/(1 − ε₀²)`,
`T_max = κ(n ε₀²/2 + a² δ₀² (1 + ε₀))`. Every term on the right is a product of a function of
`(δ, ε)` and a function of `(δ', ε')`. -/
theorem kTwo_pt (n : ℕ) {a2 δ ε δ' ε' ε₀ δ₀ : ℝ} (ha : 0 ≤ a2) (hε₀ : ε₀ < 1)
    (hε : |ε| ≤ ε₀) (hε' : |ε'| ≤ ε₀) (hδ : |δ| ≤ δ₀) (hδ' : |δ'| ≤ δ₀) :
    kTwo n a2 δ ε δ' ε' - 1 ≤
      (n / 2 * (ε * ε') + n * (1 - ε₀ ^ 2)⁻¹ / 4 * (ε ^ 2 * ε' ^ 2) + a2 * (δ * δ') +
        a2 * (1 - ε₀ ^ 2)⁻¹ * ((|δ| * |ε|) * (|δ'| * |ε'|)) + a2 / 2 * (δ ^ 2 * ε') +
        a2 / 2 * (ε * δ' ^ 2) + a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * ((δ ^ 2 * |ε|) * ε' ^ 2) +
        a2 * (1 - ε₀ ^ 2)⁻¹ / 2 * (ε ^ 2 * (δ' ^ 2 * |ε'|))) +
      exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀))) / 2 *
        (4 * ((1 - ε₀ ^ 2)⁻¹) ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2) + a2 ^ 2 * (δ ^ 2 * δ' ^ 2) +
          a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2) + a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4))) := by
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
  set Tm := κ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀)) with hTm
  have hTabs : |T| ≤ Tm := by
    have t1 : |A1| ≤ κ * (n * ε₀ ^ 2 / 2) := by
      refine c1.trans ?_
      have : κ * |w| ≤ κ * r := mul_le_mul_of_nonneg_left hwr hκ0.le
      calc (n : ℝ) / 2 * (κ * |w|) ≤ n / 2 * (κ * r) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = κ * (n * ε₀ ^ 2 / 2) := by rw [hr]; ring
    have t2 : |A2| ≤ κ * (a2 * δ₀ ^ 2) := by
      refine c2.trans ?_
      have h1 : a2 * |δ| * |δ'| ≤ a2 * δ₀ ^ 2 := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hdd ha
      have h2 := mul_le_mul h1 huκ hu0.le (by positivity)
      linarith [show a2 * δ₀ ^ 2 * κ = κ * (a2 * δ₀ ^ 2) by ring]
    have t3 : |A3| ≤ κ * (a2 / 2 * δ₀ ^ 2 * ε₀) := by
      refine c3.trans ?_
      have h1 : a2 / 2 * δ ^ 2 * |ε'| ≤ a2 / 2 * δ₀ ^ 2 * ε₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd2 (by positivity)) hε' (abs_nonneg _)
          (by positivity)
      have h2 := mul_le_mul h1 huκ hu0.le (by positivity)
      linarith [show a2 / 2 * δ₀ ^ 2 * ε₀ * κ = κ * (a2 / 2 * δ₀ ^ 2 * ε₀) by ring]
    have t4 : |A4| ≤ κ * (a2 / 2 * δ₀ ^ 2 * ε₀) := by
      refine c4.trans ?_
      have h1 : a2 / 2 * δ' ^ 2 * |ε| ≤ a2 / 2 * δ₀ ^ 2 * ε₀ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd2' (by positivity)) hε (abs_nonneg _)
          (by positivity)
      have h2 := mul_le_mul h1 huκ hu0.le (by positivity)
      linarith [show a2 / 2 * δ₀ ^ 2 * ε₀ * κ = κ * (a2 / 2 * δ₀ ^ 2 * ε₀) by ring]
    have s1 := abs_add_le (A1 + A2 + A3) A4
    have s2 := abs_add_le (A1 + A2) A3
    have s3 := abs_add_le A1 A2
    have e : κ * (n * ε₀ ^ 2 / 2) + κ * (a2 * δ₀ ^ 2) + κ * (a2 / 2 * δ₀ ^ 2 * ε₀) +
        κ * (a2 / 2 * δ₀ ^ 2 * ε₀) = Tm := by rw [hTm]; ring
    rw [hTd]
    linarith
  -- the square
  have q1 : A1 ^ 2 ≤ κ ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2)) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) c1 2
    rw [sq_abs] at h
    have e : (n / 2 * (κ * |w|)) ^ 2 = κ ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2)) := by
      rw [haw]; ring_nf; rw [sq_abs, sq_abs]
    linarith
  have hu2 : u ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hu0.le huκ 2
  have q2 : A2 ^ 2 ≤ κ ^ 2 * (a2 ^ 2 * (δ ^ 2 * δ' ^ 2)) := by
    have e : A2 ^ 2 = (a2 ^ 2 * (δ ^ 2 * δ' ^ 2)) * u ^ 2 := by rw [hA2]; ring
    rw [e, mul_comm (κ ^ 2)]; exact mul_le_mul_of_nonneg_left hu2 (by positivity)
  have q3 : A3 ^ 2 ≤ κ ^ 2 * (a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2)) := by
    have e : A3 ^ 2 = (a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2)) * u ^ 2 := by rw [hA3]; ring
    rw [e, mul_comm (κ ^ 2)]; exact mul_le_mul_of_nonneg_left hu2 (by positivity)
  have q4 : A4 ^ 2 ≤ κ ^ 2 * (a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4)) := by
    have e : A4 ^ 2 = (a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4)) * u ^ 2 := by rw [hA4]; ring
    rw [e, mul_comm (κ ^ 2)]; exact mul_le_mul_of_nonneg_left hu2 (by positivity)
  have hT2 : T ^ 2 ≤ 4 * κ ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2) + a2 ^ 2 * (δ ^ 2 * δ' ^ 2) +
      a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2) + a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4)) := by
    have h4 : T ^ 2 ≤ 4 * (A1 ^ 2 + A2 ^ 2 + A3 ^ 2 + A4 ^ 2) := by
      rw [hTd]; exact sq4_le A1 A2 A3 A4
    linarith
  -- the exponential
  have hE := exp_le_quad T
  have hmax : exp (max T 0) ≤ exp Tm := by
    refine exp_le_exp.mpr (max_le ((le_abs_self T).trans hTabs) ((abs_nonneg T).trans hTabs))
  have hEm : exp (max T 0) * T ^ 2 / 2 ≤ exp Tm / 2 * (4 * κ ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2) +
      a2 ^ 2 * (δ ^ 2 * δ' ^ 2) + a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2) +
      a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4))) := by
    have h1 : exp (max T 0) * T ^ 2 ≤ exp Tm * T ^ 2 :=
      mul_le_mul_of_nonneg_right hmax (sq_nonneg T)
    have h2 : exp Tm * T ^ 2 ≤ exp Tm * (4 * κ ^ 2 * (n ^ 2 / 4 * (ε ^ 2 * ε' ^ 2) +
        a2 ^ 2 * (δ ^ 2 * δ' ^ 2) + a2 ^ 2 / 4 * (δ ^ 4 * ε' ^ 2) +
        a2 ^ 2 / 4 * (ε ^ 2 * δ' ^ 4))) := mul_le_mul_of_nonneg_left hT2 (exp_pos _).le
    linarith
  rw [hT]
  have hTL : T ≤ n / 2 * (ε * ε') + n * κ / 4 * (ε ^ 2 * ε' ^ 2) + a2 * (δ * δ') +
      a2 * κ * ((|δ| * |ε|) * (|δ'| * |ε'|)) + a2 / 2 * (δ ^ 2 * ε') + a2 / 2 * (ε * δ' ^ 2) +
      a2 * κ / 2 * ((δ ^ 2 * |ε|) * ε' ^ 2) + a2 * κ / 2 * (ε ^ 2 * (δ' ^ 2 * |ε'|)) := by
    rw [hTd]; linarith
  linarith

section integrated

variable {V : Type*} [MeasurableSpace V]

/-- **The second-order bound of the chi-square in a uniform window (the general conclusion of
Corollary `t7:p07:chi-bounds`).** `pm` is a probability measure on the parameters; `δ`, `ε` are
measurable with `|ε| ≤ ε₀ < 1`, `|δ| ≤ δ₀`; `a² ≥ 0`. With `m_ε = E ε`, `m_δ = E δ`,
`v_ε = E ε²`, `v_δ = E δ²`, `κ = 1/(1 − ε₀²)`, `T_max = κ(n ε₀²/2 + a² δ₀²(1 + ε₀))`:
`E_{pm⊗pm} kTwo − 1 ≤ (n/2) m_ε² + a² m_δ² + a² v_δ m_ε + κ(n v_ε²/4 + a²(1 + ε₀) v_δ v_ε) +
2κ² e^{T_max}(n² v_ε²/4 + a⁴ v_δ² + a⁴ δ₀² v_δ v_ε/2)`. (The paper writes `a² v_δ |m_ε|`.) -/
theorem chi_general (pm : Measure V) [IsProbabilityMeasure pm] (n : ℕ) {a2 ε₀ δ₀ : ℝ}
    {δ ε : V → ℝ} (hδm : Measurable δ) (hεm : Measurable ε) (ha : 0 ≤ a2) (hε₀ : ε₀ < 1)
    (hwε : ∀ v, |ε v| ≤ ε₀) (hwδ : ∀ v, |δ v| ≤ δ₀) :
    ∫ w, kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) ∂(pm.prod pm) - 1 ≤
      n / 2 * (∫ v, ε v ∂pm) ^ 2 + a2 * (∫ v, δ v ∂pm) ^ 2 +
        a2 * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ∂pm) +
        (1 - ε₀ ^ 2)⁻¹ * (n * (∫ v, ε v ^ 2 ∂pm) ^ 2 / 4 +
          a2 * (1 + ε₀) * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ^ 2 ∂pm)) +
        2 * ((1 - ε₀ ^ 2)⁻¹) ^ 2 * exp ((1 - ε₀ ^ 2)⁻¹ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀))) *
          (n ^ 2 * (∫ v, ε v ^ 2 ∂pm) ^ 2 / 4 + a2 ^ 2 * (∫ v, δ v ^ 2 ∂pm) ^ 2 +
            a2 ^ 2 * δ₀ ^ 2 * (∫ v, δ v ^ 2 ∂pm) * (∫ v, ε v ^ 2 ∂pm) / 2) := by
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwε (Classical.arbitrary V))
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans (hwδ (Classical.arbitrary V))
  set κ := (1 - ε₀ ^ 2)⁻¹ with hκ
  have hd0 : 0 < 1 - ε₀ ^ 2 := by nlinarith
  have hκ0 : 0 < κ := inv_pos.mpr hd0
  set Tm := κ * (n * ε₀ ^ 2 / 2 + a2 * δ₀ ^ 2 * (1 + ε₀)) with hTm
  set cc := exp Tm / 2 * (4 * κ ^ 2) with hcc
  have hcc0 : 0 ≤ cc := by positivity
  -- integrability of bounded measurable functions
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
  have iδ4 := ibd (hδm.pow_const 4) (δ₀ ^ 4) fun v => by
    rw [abs_of_nonneg (by positivity)]
    have := pow_le_pow_left₀ (sq_nonneg _) (bδ2 v) 2
    rw [← pow_mul, ← pow_mul] at this; exact this
  -- the product rule
  have hpr : ∀ {f g : V → ℝ}, ∫ w, f w.1 * g w.2 ∂(pm.prod pm) = (∫ v, f v ∂pm) * ∫ v, g v ∂pm :=
    fun {f g} => integral_prod_mul f g
  have ipr : ∀ {f g : V → ℝ}, Integrable f pm → Integrable g pm →
      Integrable (fun w : V × V => f w.1 * g w.2) (pm.prod pm) :=
    fun {f g} hf hg => hf.mul_prod hg
  -- the pointwise bound
  set P : V × V → ℝ := fun w =>
    (n / 2 * (ε w.1 * ε w.2) + n * κ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 * (δ w.1 * δ w.2) +
      a2 * κ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) + a2 / 2 * (δ w.1 ^ 2 * ε w.2) +
      a2 / 2 * (ε w.1 * δ w.2 ^ 2) + a2 * κ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
      a2 * κ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|))) +
    exp Tm / 2 * (4 * κ ^ 2 * (n ^ 2 / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) +
      a2 ^ 2 * (δ w.1 ^ 2 * δ w.2 ^ 2) + a2 ^ 2 / 4 * (δ w.1 ^ 4 * ε w.2 ^ 2) +
      a2 ^ 2 / 4 * (ε w.1 ^ 2 * δ w.2 ^ 4))) with hP
  have hpt : ∀ w : V × V, kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) - 1 ≤ P w := fun w => by
    rw [hP]; exact kTwo_pt n ha hε₀ (hwε _) (hwε _) (hwδ _) (hwδ _)
  clear_value P
  -- the integral of `P`
  have i1 := ipr iε iε
  have i2 := ipr iε2 iε2
  have i3 := ipr iδ iδ
  have i4 := ipr iδε iδε
  have i5 := ipr iδ2 iε
  have i6 := ipr iε iδ2
  have i7 := ipr iδ2ε iε2
  have i8 := ipr iε2 iδ2ε
  have i10 := ipr iδ2 iδ2
  have i11 := ipr iδ4 iε2
  have i12 := ipr iε2 iδ4
  have hPint : ∫ w, P w ∂(pm.prod pm) =
      n / 2 * ((∫ v, ε v ∂pm) * ∫ v, ε v ∂pm) +
        n * κ / 4 * ((∫ v, ε v ^ 2 ∂pm) * ∫ v, ε v ^ 2 ∂pm) +
        a2 * ((∫ v, δ v ∂pm) * ∫ v, δ v ∂pm) +
        a2 * κ * ((∫ v, |δ v| * |ε v| ∂pm) * ∫ v, |δ v| * |ε v| ∂pm) +
        a2 / 2 * ((∫ v, δ v ^ 2 ∂pm) * ∫ v, ε v ∂pm) +
        a2 / 2 * ((∫ v, ε v ∂pm) * ∫ v, δ v ^ 2 ∂pm) +
        a2 * κ / 2 * ((∫ v, δ v ^ 2 * |ε v| ∂pm) * ∫ v, ε v ^ 2 ∂pm) +
        a2 * κ / 2 * ((∫ v, ε v ^ 2 ∂pm) * ∫ v, δ v ^ 2 * |ε v| ∂pm) +
        cc * (n ^ 2 / 4 * ((∫ v, ε v ^ 2 ∂pm) * ∫ v, ε v ^ 2 ∂pm) +
          a2 ^ 2 * ((∫ v, δ v ^ 2 ∂pm) * ∫ v, δ v ^ 2 ∂pm) +
          a2 ^ 2 / 4 * ((∫ v, δ v ^ 4 ∂pm) * ∫ v, ε v ^ 2 ∂pm) +
          a2 ^ 2 / 4 * ((∫ v, ε v ^ 2 ∂pm) * ∫ v, δ v ^ 4 ∂pm)) := by
    have eP : P = fun w =>
        n / 2 * (ε w.1 * ε w.2) + n * κ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 * (δ w.1 * δ w.2) +
        a2 * κ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) + a2 / 2 * (δ w.1 ^ 2 * ε w.2) +
        a2 / 2 * (ε w.1 * δ w.2 ^ 2) + a2 * κ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
        a2 * κ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|)) +
        cc * (n ^ 2 / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 ^ 2 * (δ w.1 ^ 2 * δ w.2 ^ 2) +
          a2 ^ 2 / 4 * (δ w.1 ^ 4 * ε w.2 ^ 2) + a2 ^ 2 / 4 * (ε w.1 ^ 2 * δ w.2 ^ 4)) := by
      funext w; rw [hP, hcc]; ring
    rw [eP]
    repeat rw [integral_add]
    all_goals try fun_prop
    simp only [integral_const_mul]
    repeat rw [integral_add]
    all_goals try fun_prop
    simp only [integral_const_mul]
    rw [integral_prod_mul ε ε, integral_prod_mul (fun v => ε v ^ 2) (fun v => ε v ^ 2),
      integral_prod_mul δ δ, integral_prod_mul (fun v => |δ v| * |ε v|) (fun v => |δ v| * |ε v|),
      integral_prod_mul (fun v => δ v ^ 2) ε, integral_prod_mul ε (fun v => δ v ^ 2),
      integral_prod_mul (fun v => δ v ^ 2 * |ε v|) (fun v => ε v ^ 2),
      integral_prod_mul (fun v => ε v ^ 2) (fun v => δ v ^ 2 * |ε v|),
      integral_prod_mul (fun v => δ v ^ 2) (fun v => δ v ^ 2),
      integral_prod_mul (fun v => δ v ^ 4) (fun v => ε v ^ 2),
      integral_prod_mul (fun v => ε v ^ 2) (fun v => δ v ^ 4)]
  -- integrability of the kernel and of `P`
  set M := (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * a2 * δ₀ ^ 2 / (1 - ε₀ ^ 2))
  have mK : Measurable (fun w : V × V => kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2)) :=
    (measurable_kTwo n).comp (measurable_const.prodMk
      (((hδm.comp measurable_fst).prodMk (hεm.comp measurable_fst)).prodMk
        ((hδm.comp measurable_snd).prodMk (hεm.comp measurable_snd))))
  have iK : Integrable (fun w : V × V => kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2))
      (pm.prod pm) :=
    Integrable.of_bound mK.aestronglyMeasurable M (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kTwo_nonneg _ _ _ _ _ _)]
      exact kTwo_le n ha hε₀ (hwε _) (hwε _) (hwδ _) (hwδ _))
  have iP : Integrable P (pm.prod pm) := by
    have eP : P = fun w =>
        n / 2 * (ε w.1 * ε w.2) + n * κ / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 * (δ w.1 * δ w.2) +
        a2 * κ * ((|δ w.1| * |ε w.1|) * (|δ w.2| * |ε w.2|)) + a2 / 2 * (δ w.1 ^ 2 * ε w.2) +
        a2 / 2 * (ε w.1 * δ w.2 ^ 2) + a2 * κ / 2 * ((δ w.1 ^ 2 * |ε w.1|) * ε w.2 ^ 2) +
        a2 * κ / 2 * (ε w.1 ^ 2 * (δ w.2 ^ 2 * |ε w.2|)) +
        cc * (n ^ 2 / 4 * (ε w.1 ^ 2 * ε w.2 ^ 2) + a2 ^ 2 * (δ w.1 ^ 2 * δ w.2 ^ 2) +
          a2 ^ 2 / 4 * (δ w.1 ^ 4 * ε w.2 ^ 2) + a2 ^ 2 / 4 * (ε w.1 ^ 2 * δ w.2 ^ 4)) := by
      funext w; rw [hP, hcc]; ring
    rw [eP]; fun_prop
  have hmain : ∫ w, kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) ∂(pm.prod pm) - 1 ≤
      ∫ w, P w ∂(pm.prod pm) := by
    have iP1 : Integrable (fun w => P w + 1) (pm.prod pm) := iP.add (integrable_const 1)
    have h1 : ∫ w, kTwo n a2 (δ w.1) (ε w.1) (δ w.2) (ε w.2) ∂(pm.prod pm) ≤
        ∫ w, (P w + 1) ∂(pm.prod pm) :=
      integral_mono iK iP1 (fun w => by have := hpt w; simp only; linarith)
    rw [integral_add iP (integrable_const 1)] at h1
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
    linarith
  rw [hPint] at hmain
  refine hmain.trans ?_
  -- the moment inequalities
  set mε := ∫ v, ε v ∂pm
  set mδ := ∫ v, δ v ∂pm
  set vε := ∫ v, ε v ^ 2 ∂pm
  set vδ := ∫ v, δ v ^ 2 ∂pm
  set X := ∫ v, |δ v| * |ε v| ∂pm
  set Y := ∫ v, δ v ^ 2 * |ε v| ∂pm
  set Z := ∫ v, δ v ^ 4 ∂pm
  have hvε : 0 ≤ vε := integral_nonneg fun v => sq_nonneg _
  have hvδ : 0 ≤ vδ := integral_nonneg fun v => sq_nonneg _
  have hX : X ^ 2 ≤ vδ * vε := by
    have h := BstLean.Part138.cs_sq pm (f := fun v => |δ v|) (g := fun v => |ε v|)
      (by simpa only [sq_abs] using iδ2) (by simpa only [sq_abs] using iε2) iδε
    simpa only [sq_abs] using h
  have hY : Y ≤ ε₀ * vδ := by
    have h := integral_mono iδ2ε (iδ2.const_mul ε₀) (fun v => by
      change δ v ^ 2 * |ε v| ≤ ε₀ * δ v ^ 2
      nlinarith [hwε v, sq_nonneg (δ v)])
    rwa [integral_const_mul] at h
  have hZ : Z ≤ δ₀ ^ 2 * vδ := by
    have h := integral_mono iδ4 (iδ2.const_mul (δ₀ ^ 2)) (fun v => by
      change δ v ^ 4 ≤ δ₀ ^ 2 * δ v ^ 2
      have : δ v ^ 4 = δ v ^ 2 * δ v ^ 2 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right (bδ2 v) (sq_nonneg _))
    rwa [integral_const_mul] at h
  have f1 : a2 * κ * (X * X) ≤ a2 * κ * (vδ * vε) :=
    mul_le_mul_of_nonneg_left (by rw [← sq]; exact hX) (mul_nonneg ha hκ0.le)
  have f2 : a2 * κ / 2 * (Y * vε) ≤ a2 * κ / 2 * (ε₀ * vδ * vε) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY hvε)
      (div_nonneg (mul_nonneg ha hκ0.le) (by norm_num))
  have f3 : cc * (a2 ^ 2 / 4 * (Z * vε)) ≤ cc * (a2 ^ 2 / 4 * (δ₀ ^ 2 * vδ * vε)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hZ hvε) (div_nonneg (sq_nonneg a2) (by norm_num))) hcc0
  have ecc : cc = 2 * κ ^ 2 * exp Tm := by rw [hcc]; ring
  clear_value mε mδ vε vδ X Y Z cc Tm κ
  subst ecc
  linear_combination f1 + 2 * f2 + 2 * f3

end integrated

end BstLean.Part161

open BstLean.Part161 in
#print axioms neg_log_le
open BstLean.Part161 in
#print axioms exp_le_quad
open BstLean.Part161 in
#print axioms kTwo_pt
open BstLean.Part161 in
#print axioms chi_general
