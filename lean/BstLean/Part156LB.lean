import BstLean.Part156Out

/-!
# Part 156 (item 6): the lower bound for rules that see only Boolean samples

A rule sees `k` independent Boolean samples, each `true` with probability `p`, and its own random
numbers. It outputs a number `U`. Model of the samples: the outcome is the set `t ⊆ {0, …, k-1}`
of the indices of the samples with value `true`; its probability is `p^|t| (1-p)^(k-|t|)`.

* `Ebin k p φ`: the expectation of a function `φ` of the outcome.
* `Testable k`: there is a test `φ` with values in `[0, 1]`, `E_{1/1000} φ ≤ 1/100` and
  `E_{1/100} φ ≥ 99/100`.
* `testable_of_rule` (the two-point reduction): a rule that succeeds with probability at least
  `99/100` at `p = 1/1000` and at every `p` in an interval `(1/100, 1/100 + ε)` gives a test.
* `testable_succ` (monotone in `k`): a test with `k` samples gives a test with `k + 1` samples.
* `not_testable_1138`: there is no test with `1138` samples (the Neyman–Pearson computation; the
  exact binomial inequalities at `k = 1138` are proved by `norm_num` on rational numbers).
* `no_sampling_rule`: for `k ≤ 1138`, no rule succeeds with probability at least `99/100` at
  `p = 1/1000` and at every `p` in `(1/100, 1/100 + ε)`.

This file does not use the networks. It has no assumed hypothesis.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open Finset MeasureTheory

/-- The expectation of `φ` under `k` independent Bernoulli(`p`) samples; the outcome `t` is the
set of the indices of the samples with value `true`. -/
noncomputable def Ebin (k : ℕ) (p : ℝ) (φ : Finset ℕ → ℝ) : ℝ :=
  ∑ t ∈ (range k).powerset, p ^ t.card * (1 - p) ^ (k - t.card) * φ t

lemma Ebin_one (k : ℕ) (p : ℝ) : Ebin k p (fun _ => 1) = 1 := by
  unfold Ebin
  have h := Finset.sum_pow_mul_eq_add_pow p (1 - p) (range k)
  rw [card_range] at h
  simp only [mul_one]
  rw [h]
  simp

/-- Monotone in `k`: a function of the first `k` samples has the same expectation under `k + 1`
samples. -/
lemma Ebin_succ (k : ℕ) (p : ℝ) (φ : Finset ℕ → ℝ) :
    Ebin (k + 1) p (fun t => φ (t.erase k)) = Ebin k p φ := by
  unfold Ebin
  rw [range_add_one, sum_powerset_insert notMem_range_self, ← sum_add_distrib]
  refine sum_congr rfl (fun t ht => ?_)
  have hsub : t ⊆ range k := mem_powerset.1 ht
  have hk : k ∉ t := fun h => notMem_range_self (hsub h)
  have hcard : t.card ≤ k := by
    have := card_le_card hsub
    rwa [card_range] at this
  beta_reduce
  rw [erase_eq_of_notMem hk, erase_insert hk, card_insert_of_notMem hk]
  have e1 : k + 1 - t.card = (k - t.card) + 1 := by omega
  have e2 : k + 1 - (t.card + 1) = k - t.card := by omega
  rw [e1, e2, pow_succ, pow_succ]
  ring

/-- There is a test with `k` samples: values in `[0, 1]`, size at most `1/100` at `p = 1/1000`,
power at least `99/100` at `p = 1/100`. -/
def Testable (k : ℕ) : Prop :=
  ∃ φ : Finset ℕ → ℝ, (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧
    Ebin k (1 / 1000) φ ≤ 1 / 100 ∧ 99 / 100 ≤ Ebin k (1 / 100) φ

/-- Monotone in `k`: a test with `k` samples gives a test with `k + 1` samples. -/
theorem testable_succ {k : ℕ} (h : Testable k) : Testable (k + 1) := by
  obtain ⟨φ, hφ, h0, h1⟩ := h
  refine ⟨fun t => φ (t.erase k), fun t => hφ _, ?_, ?_⟩
  · rw [Ebin_succ]; exact h0
  · rw [Ebin_succ]; exact h1

theorem testable_mono {k m : ℕ} (hkm : k ≤ m) (h : Testable k) : Testable m := by
  induction m, hkm using Nat.le_induction with
  | base => exact h
  | succ m _ ih => exact testable_succ ih

/-- The likelihood ratio is monotone, one step down. -/
lemma lr_step_down {p0 p1 c : ℝ} (h0 : 0 < p0) (h01 : p0 ≤ p1) (h1 : p1 < 1) (hc : 0 ≤ c)
    {k j : ℕ} (hj : j + 1 ≤ k)
    (H : p1 ^ (j + 1) * (1 - p1) ^ (k - (j + 1)) ≤ c * (p0 ^ (j + 1) * (1 - p0) ^ (k - (j + 1)))) :
    p1 ^ j * (1 - p1) ^ (k - j) ≤ c * (p0 ^ j * (1 - p0) ^ (k - j)) := by
  have e : k - j = (k - (j + 1)) + 1 := by omega
  rw [e]
  set m := k - (j + 1)
  have hp1 : 0 < p1 := lt_of_lt_of_le h0 h01
  set a := p1 ^ j * (1 - p1) ^ m with ha
  set b := c * (p0 ^ j * (1 - p0) ^ m) with hb
  have ha0 : 0 ≤ a := by have : 0 ≤ 1 - p1 := by linarith
                         positivity
  have hb0 : 0 ≤ b := by have : 0 ≤ 1 - p0 := by linarith
                         positivity
  have H' : a * p1 ≤ b * p0 := by
    have e1 : a * p1 = p1 ^ (j + 1) * (1 - p1) ^ m := by rw [ha, pow_succ]; ring
    have e2 : b * p0 = c * (p0 ^ (j + 1) * (1 - p0) ^ m) := by rw [hb, pow_succ]; ring
    rw [e1, e2]; exact H
  have h2 : a * (1 - p1) * p1 ≤ b * (1 - p0) * p1 := by
    have h3 : a * p1 * (1 - p1) ≤ b * p0 * (1 - p1) :=
      mul_le_mul_of_nonneg_right H' (by linarith)
    have h4 : b * (p0 * (1 - p1)) ≤ b * (p1 * (1 - p0)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hb0
    nlinarith
  have h5 := le_of_mul_le_mul_right h2 hp1
  calc p1 ^ j * (1 - p1) ^ (m + 1) = a * (1 - p1) := by rw [ha, pow_succ]; ring
    _ ≤ b * (1 - p0) := h5
    _ = c * (p0 ^ j * (1 - p0) ^ (m + 1)) := by rw [hb, pow_succ]; ring

/-- The likelihood ratio is monotone, one step up. -/
lemma lr_step_up {p0 p1 c : ℝ} (h0 : 0 < p0) (h01 : p0 ≤ p1) (h1 : p1 < 1) (hc : 0 ≤ c)
    {k j : ℕ} (hj : j + 1 ≤ k)
    (H : c * (p0 ^ j * (1 - p0) ^ (k - j)) ≤ p1 ^ j * (1 - p1) ^ (k - j)) :
    c * (p0 ^ (j + 1) * (1 - p0) ^ (k - (j + 1))) ≤ p1 ^ (j + 1) * (1 - p1) ^ (k - (j + 1)) := by
  have e : k - j = (k - (j + 1)) + 1 := by omega
  rw [e] at H
  set m := k - (j + 1)
  have hp1 : 0 < p1 := lt_of_lt_of_le h0 h01
  have hp0' : 0 < 1 - p0 := by linarith
  set a := p1 ^ j * (1 - p1) ^ m with ha
  set b := c * (p0 ^ j * (1 - p0) ^ m) with hb
  have ha0 : 0 ≤ a := by have : 0 ≤ 1 - p1 := by linarith
                         positivity
  have hb0 : 0 ≤ b := by positivity
  have H' : b * (1 - p0) ≤ a * (1 - p1) := by
    have e1 : a * (1 - p1) = p1 ^ j * (1 - p1) ^ (m + 1) := by rw [ha, pow_succ]; ring
    have e2 : b * (1 - p0) = c * (p0 ^ j * (1 - p0) ^ (m + 1)) := by rw [hb, pow_succ]; ring
    rw [e1, e2]; exact H
  have h2 : b * p0 * (1 - p0) ≤ a * p1 * (1 - p0) := by
    have h3 : b * (1 - p0) * p0 ≤ a * (1 - p1) * p0 := mul_le_mul_of_nonneg_right H' h0.le
    have h4 : a * ((1 - p1) * p0) ≤ a * (p1 * (1 - p0)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) ha0
    nlinarith
  have h5 := le_of_mul_le_mul_right h2 hp0'
  calc c * (p0 ^ (j + 1) * (1 - p0) ^ m) = b * p0 := by rw [hb, pow_succ]; ring
    _ ≤ a * p1 := h5
    _ = p1 ^ (j + 1) * (1 - p1) ^ m := by rw [ha, pow_succ]; ring

/-- The Neyman–Pearson bound. If the likelihood ratio is at most `c` for at most `h` hits and at
least `c` for more than `h` hits, then for every test `φ` with values in `[0, 1]`:
`E_{p1} φ - c E_{p0} φ ≤ (1 - c) - Σ_{j ≤ h} C(k, j) (P1_j - c P0_j)`. -/
lemma Ebin_np {k h : ℕ} {p0 p1 c : ℝ}
    (hlo : ∀ j, j ≤ h → j ≤ k →
      p1 ^ j * (1 - p1) ^ (k - j) ≤ c * (p0 ^ j * (1 - p0) ^ (k - j)))
    (hhi : ∀ j, h < j → j ≤ k →
      c * (p0 ^ j * (1 - p0) ^ (k - j)) ≤ p1 ^ j * (1 - p1) ^ (k - j))
    {φ : Finset ℕ → ℝ} (hφ : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1) :
    Ebin k p1 φ - c * Ebin k p0 φ ≤
      (1 - c) - ∑ j ∈ range (k + 1), (k.choose j : ℝ) *
        (if j ≤ h then p1 ^ j * (1 - p1) ^ (k - j) - c * (p0 ^ j * (1 - p0) ^ (k - j)) else 0) := by
  set x : ℕ → ℝ := fun j => p1 ^ j * (1 - p1) ^ (k - j) - c * (p0 ^ j * (1 - p0) ^ (k - j))
    with hx
  have h1 : Ebin k p1 φ - c * Ebin k p0 φ = ∑ t ∈ (range k).powerset, x t.card * φ t := by
    unfold Ebin
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl (fun t _ => ?_)
    rw [hx]; ring
  have h2 : ∑ t ∈ (range k).powerset, x t.card * φ t ≤
      ∑ t ∈ (range k).powerset, (if t.card ≤ h then 0 else x t.card) := by
    refine sum_le_sum (fun t ht => ?_)
    have hcard : t.card ≤ k := by
      have := card_le_card (mem_powerset.1 ht)
      rwa [card_range] at this
    by_cases hc : t.card ≤ h
    · simp only [hc, ↓reduceIte]
      have : x t.card ≤ 0 := by
        have := hlo _ hc hcard
        rw [hx]; simp only; linarith
      exact mul_nonpos_of_nonpos_of_nonneg this (hφ t).1
    · simp only [hc, ↓reduceIte]
      have : 0 ≤ x t.card := by
        have := hhi _ (not_le.1 hc) hcard
        rw [hx]; simp only; linarith
      calc x t.card * φ t ≤ x t.card * 1 := mul_le_mul_of_nonneg_left (hφ t).2 this
        _ = x t.card := mul_one _
  have h3 := Finset.sum_powerset_apply_card (fun j => if j ≤ h then (0 : ℝ) else x j)
    (x := range k)
  rw [card_range] at h3
  simp only [nsmul_eq_mul] at h3
  have h4 : ∑ j ∈ range (k + 1), (k.choose j : ℝ) * x j = 1 - c := by
    have ha := add_pow p1 (1 - p1) k
    have hb := add_pow p0 (1 - p0) k
    simp only [add_sub_cancel, one_pow] at ha hb
    have : ∑ j ∈ range (k + 1), (k.choose j : ℝ) * x j =
        ∑ j ∈ range (k + 1), p1 ^ j * (1 - p1) ^ (k - j) * (k.choose j : ℝ) -
          c * ∑ j ∈ range (k + 1), p0 ^ j * (1 - p0) ^ (k - j) * (k.choose j : ℝ) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl (fun j _ => ?_)
      rw [hx]; ring
    rw [this, ← ha, ← hb]; ring
  have h5 : ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (if j ≤ h then (0 : ℝ) else x j) =
      (1 - c) - ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (if j ≤ h then x j else 0) := by
    rw [← h4, ← sum_sub_distrib]
    refine sum_congr rfl (fun j _ => ?_)
    by_cases hj : j ≤ h <;> simp [hj]
  rw [h1]
  calc ∑ t ∈ (range k).powerset, x t.card * φ t
      ≤ ∑ t ∈ (range k).powerset, (if t.card ≤ h then 0 else x t.card) := h2
    _ = _ := by rw [h3, h5]

/-! ## The exact binomial inequalities at `k = 1138` -/

lemma choose_1138 : Nat.choose 1138 0 = 1 ∧ Nat.choose 1138 1 = 1138 ∧
    Nat.choose 1138 2 = 646953 ∧ Nat.choose 1138 3 = 244979536 ∧
    Nat.choose 1138 4 = 69512943340 := by
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩ <;>
    (rw [Nat.choose_eq_descFactorial_div_factorial]; norm_num [Nat.descFactorial, Nat.factorial])

/-- The likelihood ratio at `4` hits is at most `7/20`. -/
lemma lr_four : (1 / 100 : ℝ) ^ 4 * (1 - 1 / 100) ^ (1138 - 4) ≤
    7 / 20 * ((1 / 1000) ^ 4 * (1 - 1 / 1000) ^ (1138 - 4)) := by
  rw [show (1138 - 4 : ℕ) = 126 * 9 from rfl, pow_mul, pow_mul]
  norm_num

/-- The likelihood ratio at `5` hits is at least `7/20`. -/
lemma lr_five : (7 / 20 : ℝ) * ((1 / 1000) ^ 5 * (1 - 1 / 1000) ^ (1138 - 5)) ≤
    (1 / 100) ^ 5 * (1 - 1 / 100) ^ (1138 - 5) := by
  rw [show (1138 - 5 : ℕ) = 103 * 11 from rfl, pow_mul, pow_mul]
  norm_num

/-- The exact binomial inequality at `k = 1138`: the largest power of a test of size `1/100` is
below `99/100` (with the multiplier `c = 7/20` and the threshold of `4` hits). -/
lemma np_1138 : (1 - 7 / 20 : ℝ) - ∑ j ∈ range 5, (Nat.choose 1138 j : ℝ) *
      ((1 / 100) ^ j * (1 - 1 / 100) ^ (1138 - j) -
        7 / 20 * ((1 / 1000) ^ j * (1 - 1 / 1000) ^ (1138 - j))) + 7 / 20 * (1 / 100)
    < 99 / 100 := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := choose_1138
  simp only [sum_range_succ, sum_range_zero, c0, c1, c2, c3, c4]
  rw [show (1138 - 0 : ℕ) = 126 * 9 + 4 from rfl, show (1138 - 1 : ℕ) = 126 * 9 + 3 from rfl,
    show (1138 - 2 : ℕ) = 126 * 9 + 2 from rfl, show (1138 - 3 : ℕ) = 126 * 9 + 1 from rfl,
    show (1138 - 4 : ℕ) = 126 * 9 from rfl]
  simp only [pow_add, pow_mul]
  norm_num

/-- There is no test with `1138` samples. -/
theorem not_testable_1138 : ¬ Testable 1138 := by
  rintro ⟨φ, hφ, h0, h1⟩
  have hlo : ∀ j, j ≤ 4 → j ≤ 1138 → (1 / 100 : ℝ) ^ j * (1 - 1 / 100) ^ (1138 - j) ≤
      7 / 20 * ((1 / 1000) ^ j * (1 - 1 / 1000) ^ (1138 - j)) := by
    have key : ∀ d, d ≤ 4 → (1 / 100 : ℝ) ^ (4 - d) * (1 - 1 / 100) ^ (1138 - (4 - d)) ≤
        7 / 20 * ((1 / 1000) ^ (4 - d) * (1 - 1 / 1000) ^ (1138 - (4 - d))) := by
      intro d
      induction d with
      | zero => intro _; exact lr_four
      | succ d ih =>
        intro hd
        have h := ih (by omega)
        have e : 4 - d = (4 - (d + 1)) + 1 := by omega
        rw [e] at h
        exact lr_step_down (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by omega) h
    intro j hj _
    have := key (4 - j) (by omega)
    have e : 4 - (4 - j) = j := by omega
    rwa [e] at this
  have hhi : ∀ j, 4 < j → j ≤ 1138 →
      (7 / 20 : ℝ) * ((1 / 1000) ^ j * (1 - 1 / 1000) ^ (1138 - j)) ≤
        (1 / 100) ^ j * (1 - 1 / 100) ^ (1138 - j) := by
    have key : ∀ d, 5 + d ≤ 1138 →
        (7 / 20 : ℝ) * ((1 / 1000) ^ (5 + d) * (1 - 1 / 1000) ^ (1138 - (5 + d))) ≤
          (1 / 100) ^ (5 + d) * (1 - 1 / 100) ^ (1138 - (5 + d)) := by
      intro d
      induction d with
      | zero => intro _; exact lr_five
      | succ d ih =>
        intro hd
        have h := ih (by omega)
        exact lr_step_up (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by omega) h
    intro j hj hj'
    have := key (j - 5) (by omega)
    have e : 5 + (j - 5) = j := by omega
    rwa [e] at this
  have hnp := Ebin_np hlo hhi hφ
  have hsum : ∑ j ∈ range (1138 + 1), (Nat.choose 1138 j : ℝ) *
      (if j ≤ 4 then (1 / 100 : ℝ) ^ j * (1 - 1 / 100) ^ (1138 - j) -
        7 / 20 * ((1 / 1000) ^ j * (1 - 1 / 1000) ^ (1138 - j)) else 0) =
      ∑ j ∈ range 5, (Nat.choose 1138 j : ℝ) *
        ((1 / 100) ^ j * (1 - 1 / 100) ^ (1138 - j) -
          7 / 20 * ((1 / 1000) ^ j * (1 - 1 / 1000) ^ (1138 - j))) := by
    have hsub : range 5 ⊆ range (1138 + 1) := range_subset_range.2 (by norm_num)
    rw [← sum_subset hsub]
    · refine sum_congr rfl (fun j hj => ?_)
      have : j ≤ 4 := by have := mem_range.1 hj; omega
      simp only [this, ↓reduceIte]
    · intro j _ hj
      have : ¬ j ≤ 4 := by
        intro h; exact hj (mem_range.2 (by omega))
      simp only [this, ↓reduceIte, mul_zero]
  rw [hsum] at hnp
  have := np_1138
  nlinarith

/-- For `k ≤ 1138` there is no test with `k` samples. -/
theorem not_testable_le {k : ℕ} (hk : k ≤ 1138) : ¬ Testable k :=
  fun h => not_testable_1138 (testable_mono hk h)

/-! ## The two-point reduction for a randomized rule -/

section rule

variable {Θ : Type*} [MeasurableSpace Θ]

/-- The success probability at `p` of a randomized rule `U` that sees `k` Boolean samples.
`U t θ` is the output at the outcome `t` and the internal random element `θ` (distribution `ν`). -/
noncomputable def succP (k : ℕ) (ν : Measure Θ) (U : Finset ℕ → Θ → ℝ) (p : ℝ) : ℝ :=
  ∑ t ∈ (range k).powerset, p ^ t.card * (1 - p) ^ (k - t.card) *
    ν.real {θ | success p (U t θ)}

/-- **The two-point reduction.** A rule that succeeds with probability at least `99/100` at
`p = 1/1000` and at every `p` in `(1/100, 1/100 + ε)` gives a test:
`φ t` is the probability that the output is above `1/100`. -/
theorem testable_of_rule {k : ℕ} (ν : Measure Θ) [IsProbabilityMeasure ν]
    {U : Finset ℕ → Θ → ℝ} (hU : ∀ t, Measurable (U t)) {ε : ℝ} (hε : 0 < ε)
    (h0 : 99 / 100 ≤ succP k ν U (1 / 1000))
    (h1 : ∀ p : ℝ, 1 / 100 < p → p < 1 / 100 + ε → 99 / 100 ≤ succP k ν U p) :
    Testable k := by
  set φ : Finset ℕ → ℝ := fun t => ν.real {θ | 1 / 100 < U t θ} with hφ
  have hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1 := fun t => ⟨measureReal_nonneg, measureReal_le_one⟩
  refine ⟨φ, hφ01, ?_, ?_⟩
  · -- size
    have hle : succP k ν U (1 / 1000) ≤ Ebin k (1 / 1000) (fun t => 1 - φ t) := by
      unfold succP Ebin
      refine sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left ?_ (by positivity))
      have hm : MeasurableSet {θ | 1 / 100 < U t θ} := measurableSet_lt measurable_const (hU t)
      have : (1 : ℝ) - φ t = ν.real {θ | 1 / 100 < U t θ}ᶜ := by
        rw [measureReal_compl hm, probReal_univ]
      show ν.real {θ | success (1 / 1000) (U t θ)} ≤ 1 - φ t
      rw [this]
      refine measureReal_mono (fun θ hθ => ?_)
      have h2 : U t θ ≤ max (10 * (1 / 1000)) (1 / 100) := hθ.2
      have h3 : max (10 * (1 / 1000 : ℝ)) (1 / 100) = 1 / 100 := by norm_num
      rw [h3] at h2
      exact not_lt.2 h2
    have hsplit : Ebin k (1 / 1000) (fun t => 1 - φ t) = 1 - Ebin k (1 / 1000) φ := by
      have h1 := Ebin_one k (1 / 1000)
      unfold Ebin at h1 ⊢
      simp only [mul_one] at h1
      simp only [mul_sub, mul_one, sum_sub_distrib]
      rw [h1]
    linarith
  · -- power, by continuity in `p`
    have hcont : Continuous fun p : ℝ => Ebin k p φ := by
      unfold Ebin
      exact continuous_finsetSum _ (fun t _ => by fun_prop)
    have hev : ∀ᶠ p in nhdsWithin (1 / 100 : ℝ) (Set.Ioi (1 / 100)), 99 / 100 ≤ Ebin k p φ := by
      have hmem : Set.Ioo (1 / 100 : ℝ) (1 / 100 + min ε (1 / 2)) ∈
          nhdsWithin (1 / 100 : ℝ) (Set.Ioi (1 / 100)) :=
        Ioo_mem_nhdsGT (by have := lt_min hε (by norm_num : (0 : ℝ) < 1 / 2); linarith)
      filter_upwards [hmem] with p hp
      have hp1 : 1 / 100 < p := hp.1
      have hp2 : p < 1 / 100 + ε := lt_of_lt_of_le hp.2 (by have := min_le_left ε (1 / 2); linarith)
      have hp3 : p < 1 := lt_of_lt_of_le hp.2 (by have := min_le_right ε (1 / 2 : ℝ); linarith)
      refine (h1 p hp1 hp2).trans ?_
      unfold succP Ebin
      refine sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left ?_ ?_)
      · refine measureReal_mono (fun θ hθ => ?_)
        have h2 : p ≤ U t θ := hθ.1
        exact lt_of_lt_of_le hp1 h2
      · have : 0 ≤ p := by linarith
        have : 0 ≤ 1 - p := by linarith
        positivity
    exact ge_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- **The Boolean sampling lower bound.** For `k ≤ 1138`, no randomized rule that sees `k`
Boolean samples succeeds with probability at least `99/100` both at `p = 1/1000` and at every `p`
in an interval `(1/100, 1/100 + ε)`. -/
theorem no_sampling_rule {k : ℕ} (hk : k ≤ 1138) (ν : Measure Θ) [IsProbabilityMeasure ν]
    {U : Finset ℕ → Θ → ℝ} (hU : ∀ t, Measurable (U t)) {ε : ℝ} (hε : 0 < ε) :
    ¬ (99 / 100 ≤ succP k ν U (1 / 1000) ∧
      ∀ p : ℝ, 1 / 100 < p → p < 1 / 100 + ε → 99 / 100 ≤ succP k ν U p) :=
  fun h => not_testable_le hk (testable_of_rule ν hU hε h.1 h.2)

end rule

end BstLean.Part156
