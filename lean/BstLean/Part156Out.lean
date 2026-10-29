import Mathlib

/-!
# Part 156 (item 1): the output rule of the classifier program (deterministic)

The program of the classifier question outputs `U = min 1 (max (1/100) (a * R))`, where `R` is a
hit fraction. The program succeeds when `p ≤ U ≤ max (10 p) (1/100)`.

This file has only deterministic statements about real numbers. `Q` is the quantity that `R`
estimates on the square-root scale: `|√R - √Q| ≤ h`.

* `not_le_outRule`: if `p > U` then `p > 1/100` and `p > zplus a h Q`.
* `not_outRule_le`: if `U > max (10 p) (1/100)` then `p < 1/10`, `p < zminus a h Q` and
  `zminus a h Q > 1/1000`.
* `not_success`: failure of `success` implies one of the two events.
* `le_wplus_zplus`, `wminus_zminus`: the relation between `Q` and the thresholds that the
  endpoint reduction uses.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open Real

/-- The success criterion of the classifier question: `p ≤ U ≤ max (10 p) (1/100)`. -/
def success (p U : ℝ) : Prop := p ≤ U ∧ U ≤ max (10 * p) (1 / 100)

/-- The output rule: `U = min 1 (max (1/100) (a * R))`. -/
noncomputable def outRule (a R : ℝ) : ℝ := min 1 (max (1 / 100) (a * R))

/-- The upper threshold: `z_+(Q) = max (1/100) (a * (max 0 (√Q - h))^2)`. -/
noncomputable def zplus (a h Q : ℝ) : ℝ := max (1 / 100) (a * (max 0 (√Q - h)) ^ 2)

/-- The lower threshold: `z_-(Q) = (a/10) * (√Q + h)^2`. -/
noncomputable def zminus (a h Q : ℝ) : ℝ := a / 10 * (√Q + h) ^ 2

lemma outRule_le_one (a R : ℝ) : outRule a R ≤ 1 := min_le_left _ _

lemma zplus_ge (a h Q : ℝ) : 1 / 100 ≤ zplus a h Q := le_max_left _ _

/-- (i) Undercoverage. If `p ≤ 1`, `R ≥ 0`, `a > 0`, `|√R - √Q| ≤ h` and `p > outRule a R`,
then `p > 1/100` and `p > zplus a h Q`. -/
theorem not_le_outRule {p Q R a h : ℝ} (hp1 : p ≤ 1) (hR : 0 ≤ R) (ha : 0 < a)
    (hRQ : |√R - √Q| ≤ h) (hfail : ¬ p ≤ outRule a R) :
    1 / 100 < p ∧ zplus a h Q < p := by
  unfold outRule at hfail
  have h1 : max (1 / 100) (a * R) < p := by
    rcases min_lt_iff.1 (not_le.1 hfail) with h | h
    · linarith
    · exact h
  have h100 : 1 / 100 < p := lt_of_le_of_lt (le_max_left _ _) h1
  have haR : a * R < p := lt_of_le_of_lt (le_max_right _ _) h1
  refine ⟨h100, ?_⟩
  have hsq : max 0 (√Q - h) ≤ √R := by
    refine max_le (Real.sqrt_nonneg _) ?_
    have := (abs_le.1 hRQ).1
    linarith
  have hR2 : (max 0 (√Q - h)) ^ 2 ≤ R := by
    calc (max 0 (√Q - h)) ^ 2 ≤ (√R) ^ 2 := by
          exact pow_le_pow_left₀ (le_max_left _ _) hsq 2
      _ = R := Real.sq_sqrt hR
  unfold zplus
  refine max_lt h100 (lt_of_le_of_lt ?_ haR)
  exact mul_le_mul_of_nonneg_left hR2 ha.le

/-- (ii) Excess output. If `R ≥ 0`, `a > 0`, `|√R - √Q| ≤ h` and
`outRule a R > max (10 p) (1/100)`, then `p < 1/10`, `p < zminus a h Q` and
`zminus a h Q > 1/1000`. -/
theorem not_outRule_le {p Q R a h : ℝ} (hR : 0 ≤ R) (ha : 0 < a)
    (hRQ : |√R - √Q| ≤ h) (hfail : ¬ outRule a R ≤ max (10 * p) (1 / 100)) :
    p < 1 / 10 ∧ p < zminus a h Q ∧ 1 / 1000 < zminus a h Q := by
  have hf := not_le.1 hfail
  have h1 : max (10 * p) (1 / 100) < 1 := lt_of_lt_of_le hf (outRule_le_one a R)
  have hp10 : 10 * p < 1 := lt_of_le_of_lt (le_max_left _ _) h1
  have h2 : max (10 * p) (1 / 100) < max (1 / 100) (a * R) :=
    lt_of_lt_of_le hf (min_le_right _ _)
  have h3 : max (10 * p) (1 / 100) < a * R := by
    rcases lt_max_iff.1 h2 with h | h
    · exact absurd h (not_lt.2 (le_max_right _ _))
    · exact h
  have hsq : √R ≤ √Q + h := by
    have := (abs_le.1 hRQ).2
    linarith
  have hR2 : R ≤ (√Q + h) ^ 2 := by
    calc R = (√R) ^ 2 := (Real.sq_sqrt hR).symm
      _ ≤ (√Q + h) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
  have h4 : a * R ≤ a * (√Q + h) ^ 2 := mul_le_mul_of_nonneg_left hR2 ha.le
  have h5 : 10 * p < a * (√Q + h) ^ 2 := lt_of_le_of_lt (le_max_left _ _) (h3.trans_le h4)
  have h6 : 1 / 100 < a * (√Q + h) ^ 2 := lt_of_le_of_lt (le_max_right _ _) (h3.trans_le h4)
  unfold zminus
  refine ⟨by linarith, by linarith, by linarith⟩

/-- Failure of `success` implies one of two explicit events: `p > z_+(Q)` (and `p > 1/100`), or
`p < z_-(Q)` with `z_-(Q) > 1/1000` (and `p < 1/10`). -/
theorem not_success {p Q R a h : ℝ} (hp1 : p ≤ 1) (hR : 0 ≤ R) (ha : 0 < a)
    (hRQ : |√R - √Q| ≤ h) (hfail : ¬ success p (outRule a R)) :
    (1 / 100 < p ∧ zplus a h Q < p) ∨
      (p < 1 / 10 ∧ p < zminus a h Q ∧ 1 / 1000 < zminus a h Q) := by
  unfold success at hfail
  by_cases h1 : p ≤ outRule a R
  · right
    exact not_outRule_le hR ha hRQ (fun h2 => hfail ⟨h1, h2⟩)
  · left
    exact not_le_outRule hp1 hR ha hRQ h1

/-- The anchor of the upper tail: `w_+(z) = (√(z/a) + h)^2`. -/
noncomputable def wplus (a h z : ℝ) : ℝ := (√(z / a) + h) ^ 2

/-- The anchor of the lower tail: `w_-(z) = (√(10 z/a) - h)^2`. -/
noncomputable def wminus (a h z : ℝ) : ℝ := (√(10 * z / a) - h) ^ 2

/-- At the deterministic threshold `z = z_+(Q)`: `Q ≤ w_+(z) = (√(z/a) + h)^2`. -/
theorem le_wplus_zplus {Q a h : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) :
    Q ≤ wplus a h (zplus a h Q) := by
  have hz : a * (max 0 (√Q - h)) ^ 2 ≤ zplus a h Q := le_max_right _ _
  have h1 : (max 0 (√Q - h)) ^ 2 ≤ zplus a h Q / a := by
    rw [le_div_iff₀ ha]; linarith
  have h2 : max 0 (√Q - h) ≤ √(zplus a h Q / a) := Real.le_sqrt_of_sq_le h1
  have h3 : √Q ≤ √(zplus a h Q / a) + h := by
    have := le_max_right 0 (√Q - h)
    linarith
  unfold wplus
  calc Q = (√Q) ^ 2 := (Real.sq_sqrt hQ).symm
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h3 2

/-- At the deterministic threshold `z = z_-(Q)`: `√(10 z/a) = √Q + h`. -/
theorem sqrt_ten_zminus {Q a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) :
    √(10 * zminus a h Q / a) = √Q + h := by
  have : 10 * zminus a h Q / a = (√Q + h) ^ 2 := by
    unfold zminus; field_simp
  rw [this, Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) hh)]

/-- At the deterministic threshold `z = z_-(Q)`: `Q = w_-(z) = (√(10 z/a) - h)^2`. -/
theorem wminus_zminus {Q a h : ℝ} (hQ : 0 ≤ Q) (ha : 0 < a) (hh : 0 ≤ h) :
    wminus a h (zminus a h Q) = Q := by
  unfold wminus
  rw [sqrt_ten_zminus ha hh]
  simp [Real.sq_sqrt hQ]

end BstLean.Part156
