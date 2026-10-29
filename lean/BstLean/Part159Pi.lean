import BstLean.Part159PaperC

/-!
# Part 159 (file `Pi`): the hypothesis `ConstC` on the constant `c̃_N` is PROVED

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-01-statement-program.tex`, step 1 (`π̃ = 16·A_T(1/5) − 4·A_T(1/239)` with
`T = T_π`, Machin's formula; `c̃_N = π̃⁻¹·∏ 2j/(2j+1)`).

* `ATsum_err`: `|A_T(x) − arctan x| ≤ x·x^{2T}/(1 − x²)` for `0 ≤ x < 1`.
* `piT_err`: `|π̃ − π| ≤ 4·(1/25)^{T_π}`; `Tpi_spec`: `10²³·(2n)² ≤ 25^{T_π}`;
  `piT_close`: `|π̃ − π| ≤ 1/(10²³·n²)`.
* `cNt_close`: `|c̃_N − c_N| ≤ c_N/(3·10²³·n²)` for `N = 2n`, `n ≥ 1`.
* **`constC`**: `ConstC n` for every `n ≥ 13 225`.
-/

namespace BstLean.Part159

open MeasureTheory Real
open BstLean.Part130
open BstLean.Part137 (cN)
open BstLean.Part141 (cN_nonneg)
open BstLean.Part157 (cNt piT ATsum Tpi)

/-- The partial sum of the inverse tangent series against the inverse tangent. -/
theorem ATsum_err (T : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |ATsum T x - arctan x| ≤ x * (x ^ 2) ^ T / (1 - x ^ 2) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg hx0]; exact hx1)
  have hx2 : x ^ 2 < 1 := by nlinarith
  have hb : ∀ j : ℕ, ‖(-1 : ℝ) ^ j * x ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)‖ ≤
      x * (x ^ 2) ^ j := by
    intro j
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (pow_nonneg hx0 _), abs_of_nonneg (Nat.cast_nonneg _)]
    have h1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j + 1)
    have e : x ^ (2 * j + 1) = x * (x ^ 2) ^ j := by rw [pow_succ, pow_mul]; ring
    rw [e]
    exact div_le_self (by positivity) h1
  have h := norm_sub_le_of_geometric_bound_of_hasSum hx2 hb hs T
  rw [Real.norm_eq_abs] at h
  have e : ATsum T x = ∑ j ∈ Finset.range T,
      (-1 : ℝ) ^ j * x ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
    unfold ATsum
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rfl
  rw [e]
  exact h

/-- Machin's formula in the form of the program: `π = 16·arctan(1/5) − 4·arctan(1/239)`. -/
lemma machin : π = 16 * arctan (1 / 5) - 4 * arctan (1 / 239) := by
  have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [inv_eq_one_div, inv_eq_one_div] at h
  linarith

/-- **`|π̃ − π| ≤ 4·(1/25)^{T_π}`.** -/
theorem piT_err (n : ℕ) : |piT n - π| ≤ 4 * (1 / 25 : ℝ) ^ Tpi n := by
  have h1 := ATsum_err (Tpi n) (x := 1 / 5) (by norm_num) (by norm_num)
  have h2 := ATsum_err (Tpi n) (x := 1 / 239) (by norm_num) (by norm_num)
  have e1 : ((1 / 5 : ℝ) ^ 2) = 1 / 25 := by norm_num
  have e2 : ((1 / 239 : ℝ) ^ 2) ^ Tpi n ≤ (1 / 25 : ℝ) ^ Tpi n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [e1] at h1
  have hp : (0 : ℝ) ≤ (1 / 25 : ℝ) ^ Tpi n := by positivity
  have h2' : |ATsum (Tpi n) (1 / 239) - arctan (1 / 239)| ≤
      1 / 239 * (1 / 25 : ℝ) ^ Tpi n / (1 - (1 / 239) ^ 2) := by
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left e2 (by norm_num)) (by norm_num)
  have e : piT n - π = 16 * (ATsum (Tpi n) (1 / 5) - arctan (1 / 5)) -
      4 * (ATsum (Tpi n) (1 / 239) - arctan (1 / 239)) := by
    unfold piT
    rw [machin]
    ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have a1 : 16 * |ATsum (Tpi n) (1 / 5) - arctan (1 / 5)| ≤
      16 * (1 / 5 * (1 / 25 : ℝ) ^ Tpi n / (1 - 1 / 25)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have a2 : 4 * |ATsum (Tpi n) (1 / 239) - arctan (1 / 239)| ≤
      4 * (1 / 239 * (1 / 25 : ℝ) ^ Tpi n / (1 - (1 / 239) ^ 2)) :=
    mul_le_mul_of_nonneg_left h2' (by norm_num)
  have a3 : 16 * (1 / 5 * (1 / 25 : ℝ) ^ Tpi n / (1 - 1 / 25)) +
      4 * (1 / 239 * (1 / 25 : ℝ) ^ Tpi n / (1 - (1 / 239) ^ 2)) ≤
      4 * (1 / 25 : ℝ) ^ Tpi n := by
    have e3 : 16 * (1 / 5 * (1 / 25 : ℝ) ^ Tpi n / (1 - 1 / 25)) +
        4 * (1 / 239 * (1 / 25 : ℝ) ^ Tpi n / (1 - (1 / 239) ^ 2)) =
        (16 * (1 / 5) / (1 - 1 / 25) + 4 * (1 / 239) / (1 - (1 / 239) ^ 2)) *
          (1 / 25 : ℝ) ^ Tpi n := by ring
    rw [e3]
    exact mul_le_mul_of_nonneg_right (by norm_num) hp
  linarith

/-- The defining property of `T_π`: `10²³·(2n)² ≤ 25^{T_π}`. -/
theorem Tpi_spec (n : ℕ) : 10 ^ 23 * (2 * n) ^ 2 ≤ 25 ^ Tpi n := by
  have hne : {T : ℕ | 1 ≤ T ∧ 10 ^ 23 * (2 * n) ^ 2 ≤ 25 ^ T}.Nonempty := by
    refine ⟨10 ^ 23 * (2 * n) ^ 2 + 1, by omega, ?_⟩
    have h := Nat.lt_pow_self (by norm_num : 1 < 25) (n := 10 ^ 23 * (2 * n) ^ 2 + 1)
    omega
  exact (Nat.sInf_mem hne).2

/-- **`|π̃ − π| ≤ 1/(10²³·n²)`** for `n ≥ 1`. -/
theorem piT_close {n : ℕ} (hn : 1 ≤ n) : |piT n - π| ≤ 1 / (10 ^ 23 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h := piT_err n
  have hs : ((10 ^ 23 * (2 * n) ^ 2 : ℕ) : ℝ) ≤ ((25 ^ Tpi n : ℕ) : ℝ) := by
    exact_mod_cast Tpi_spec n
  push_cast at hs
  have h25 : (0 : ℝ) < (25 : ℝ) ^ Tpi n := by positivity
  have e : (1 / 25 : ℝ) ^ Tpi n = 1 / (25 : ℝ) ^ Tpi n := by rw [one_div, inv_pow, one_div]
  rw [e] at h
  refine h.trans ?_
  rw [mul_one_div, div_le_div_iff₀ h25 (by positivity)]
  nlinarith

/-- **`|c̃_N − c_N| ≤ c_N/(3·10²³·n²)`**, `N = 2n`, `n ≥ 1`. -/
theorem cNt_close {n : ℕ} (hn : 1 ≤ n) :
    |cNt n - cN (2 * n)| ≤ cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp := piT_close hn
  have hc0 := cN_nonneg (2 * n)
  have hsmall : 1 / (10 ^ 23 * (n : ℝ) ^ 2) ≤ 1 / 10 ^ 23 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hpi3 : (3 : ℝ) ≤ piT n := by
    have h1 := (abs_le.mp hp).1
    have h2 := Real.pi_gt_d2
    have h3 : (1 : ℝ) / 10 ^ 23 ≤ 1 / 10 := by norm_num
    linarith
  have hpos : (0 : ℝ) < piT n := by linarith
  have e : cNt n - cN (2 * n) = cN (2 * n) * (π - piT n) / piT n := by
    rw [cNt_eq hn]
    field_simp
  rw [e, abs_div, abs_mul, abs_of_nonneg hc0, abs_of_pos hpos, abs_sub_comm,
    div_le_iff₀ hpos]
  have h4 : cN (2 * n) * |piT n - π| ≤ cN (2 * n) * (1 / (10 ^ 23 * (n : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hp hc0
  have h5 : cN (2 * n) * (1 / (10 ^ 23 * (n : ℝ) ^ 2)) ≤
      cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * piT n := by
    have e2 : cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) * piT n =
        cN (2 * n) * (1 / (10 ^ 23 * (n : ℝ) ^ 2)) * (piT n / 3) := by
      field_simp
    rw [e2]
    have h6 : (1 : ℝ) ≤ piT n / 3 := by rw [le_div_iff₀ (by norm_num)]; linarith
    have h7 : (0 : ℝ) ≤ cN (2 * n) * (1 / (10 ^ 23 * (n : ℝ) ^ 2)) := by positivity
    nlinarith
  linarith

/-- **The hypothesis `ConstC n` holds for every `n ≥ 13 225`.** -/
theorem constC {n : ℕ} (hn : 13225 ≤ n) : ConstC n := by
  have hn' : (13225 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hc := cNt_close (n := n) (by omega)
  obtain ⟨-, hcw⟩ := cN_even_window hn
  have hc0 := cN_nonneg (2 * n)
  have hm : mW n ≤ n ^ 4 := by
    rw [mW_le_iff]
    calc n ^ 7 ≤ n ^ 7 * n := Nat.le_mul_of_pos_right _ (by omega)
      _ = (n ^ 4) ^ 2 := by ring
  have hm' : (mW n : ℝ) ≤ (n : ℝ) ^ 4 := by exact_mod_cast hm
  have hsq : (cNt n - cN (2 * n)) ^ 2 ≤ (cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2)) ^ 2 := by
    rw [← sq_abs (cNt n - cN (2 * n))]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have hsq2 : (cN (2 * n) / (3 * 10 ^ 23 * (n : ℝ) ^ 2)) ^ 2 ≤
      8 / (100 * (n : ℝ)) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hcw (by positivity)
  unfold ConstC
  have h1 : (cNt n - cN (2 * n)) ^ 2 * (n : ℝ) * (mW n : ℝ) ≤
      8 / (100 * (n : ℝ)) / (3 * 10 ^ 23 * (n : ℝ) ^ 2) ^ 2 * (n : ℝ) * (n : ℝ) ^ 4 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (hsq.trans hsq2) hnpos.le) hm' (Nat.cast_nonneg _)
      (by positivity)
  refine h1.trans (le_of_eq_of_le ?_ ?_ (b := (8 : ℝ) / (100 * 9 * 10 ^ 46)))
  · field_simp
    norm_num
  · norm_num

end BstLean.Part159

open BstLean.Part159 in
#print axioms piT_close
open BstLean.Part159 in
#print axioms cNt_close
open BstLean.Part159 in
#print axioms constC
