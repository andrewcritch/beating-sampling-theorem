import BstLean.Part176All

/-!
# Part 182 (file `W128x21`): the layered bound of the radius moment `W₁₂₈` at `n ≥ 21 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 181's file `W128` at `n ≥ 21 000`: Part 176's `WqN_le_layer` at `q = 128` with
the twenty levels `ε_k = 0.0053·min(k, 20)`:
**`W128_le_21`**: `E[(τ²/|c' + τξ|²)¹²⁸] ≤ (1.0240·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 21 000`,
`0.46 ≤ θ ≤ 0.528` and every `c'` with `|c'| = |c|`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part160 (WqN)
open BstLean.Part176 (fL fL_mono WqN_le_layer exp_neg_quart')

variable {n : ℕ}

/-- The levels `ε_k = 0.0042·min(k, 20)`. -/
noncomputable def epsW21 (k : ℕ) : ℝ := 53 / 10000 * ((min k 20 : ℕ) : ℝ)

lemma epsW21_mono (k : ℕ) : epsW21 k ≤ epsW21 (k + 1) := by
  unfold epsW21
  have : ((min k 20 : ℕ) : ℝ) ≤ ((min (k + 1) 20 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 20 (Nat.le_succ k)
  linarith

lemma epsW21_lt (k : ℕ) : epsW21 k < 1 := by
  unfold epsW21
  have : ((min k 20 : ℕ) : ℝ) ≤ 20 := by exact_mod_cast min_le_right k 20
  linarith

/-- `fL 128 τ Q e = (τ²/Q)¹²⁸·((1 − e)²)^{−128}`. -/
lemma fL_eqW21 {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 128 τ Q e = (τ ^ 2 / Q) ^ 128 * (1 / ((1 - e) ^ 2) ^ 128) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 128 = (1 / (1 - e) ^ 2) ^ 128 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp

/-- `C(e) = ((1 − e)²)^{−128}`. -/
noncomputable def CW21 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 128

/-- The tail bound `P(e) = (1 + x/4 + (x/4)²/2)^{−4}` at `x = 32 196·e²`. -/
noncomputable def PW21 (e : ℝ) : ℝ :=
  1 / (1 + e ^ 2 * 19800 / 4 + (e ^ 2 * 19800 / 4) ^ 2 / 2) ^ 4

lemma sumW21_le : ∑ k ∈ Finset.range 20, (CW21 (epsW21 (k + 1)) - CW21 (epsW21 k)) * PW21 (epsW21 k) ≤
    19713 / 1000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, epsW21, CW21, PW21]
  norm_num

/-- **`E[(τ²/|c' + τξ|²)¹²⁸] ≤ (1.0172·τ²/(|c|² + nτ²))¹²⁸`** for `n ≥ 34 000`,
`0.46 ≤ θ ≤ 0.528`, `|c'| = |c|` (the layered bound with twenty levels `ε_k = 0.0042k`). -/
theorem W128_le_21 (hn : 21000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ)
    (hθ1 : BstLean.Part150.thetaC c τ ≤ 528 / 1000) :
    WqN 128 c' τ ≤ (10240 / 10000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 := by
  have hnR : (21000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le_layer (q := 128) (by omega) c' hτ epsW21 20 (by unfold epsW21; norm_num)
    epsW21_mono epsW21_lt
  rw [hc] at h
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : BstLean.Part150.thetaC c τ = (n : ℝ) * T / R := by
    unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1
  rw [← hR, ← hT]
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [show normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 = R - T by rw [hR, hT]] at h
  rw [← hT] at h
  have hT45 : 21000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  set w := T / (R - T) with hw
  have hw0 : 0 < w := div_pos hT0 hQ0
  have hlam : 19800 ≤ (R - T) / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : ∀ k, exp (-(epsW21 k ^ 2 * (R - T)) / (2 * T)) ≤ PW21 (epsW21 k) := by
    intro k
    rw [neg_div]
    refine exp_neg_quart' (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hfL : ∀ k, fL 128 τ (R - T) (epsW21 k) = w ^ 128 * CW21 (epsW21 k) := fun k => by
    rw [fL_eqW21 hQ0 (epsW21_lt k), CW21, hw, ← hT]
  have hsum : ∑ k ∈ Finset.range 20, (fL 128 τ (R - T) (epsW21 (k + 1)) -
      fL 128 τ (R - T) (epsW21 k)) * exp (-(epsW21 k ^ 2 * (R - T)) / (2 * T)) ≤
      w ^ 128 * (19713 / 1000) := by
    calc _ ≤ ∑ k ∈ Finset.range 20, (fL 128 τ (R - T) (epsW21 (k + 1)) -
          fL 128 τ (R - T) (epsW21 k)) * PW21 (epsW21 k) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hE k)
              (by linarith [fL_mono (q := 128) (τ := τ) hQ0 (epsW21_mono k) (epsW21_lt (k + 1))])
      _ = w ^ 128 * ∑ k ∈ Finset.range 20, (CW21 (epsW21 (k + 1)) - CW21 (epsW21 k)) * PW21 (epsW21 k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hfL, hfL]; ring
      _ ≤ w ^ 128 * (19713 / 1000) := mul_le_mul_of_nonneg_left sumW21_le (by positivity)
  have h0 : fL 128 τ (R - T) (epsW21 0) = w ^ 128 := by
    rw [hfL]; unfold CW21 epsW21; norm_num
  -- the tail
  have he20 : epsW21 20 = 106 / 1000 := by unfold epsW21; norm_num
  have htl : √(exp (-(epsW21 20 ^ 2 * (R - T)) / (2 * T))) ≤ (36788 / 100000) ^ 111 := by
    have h40 : exp (-(epsW21 20 ^ 2 * (R - T)) / (2 * T)) ≤ exp (-1) ^ 222 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [he20, neg_div, mul_div_assoc]
      have : (222 : ℝ) ≤ (106 / 1000) ^ 2 * ((R - T) / (2 * T)) := by nlinarith
      push_cast; linarith
    have h1 : exp (-1) ≤ 36788 / 100000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : exp (-1) ^ 222 ≤ ((36788 / 100000 : ℝ) ^ 111) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (exp_pos _).le h1 _
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (36788 / 100000) ^ 111 by positivity)]
    exact Real.sqrt_le_sqrt (h40.trans h2)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (128 : ℕ) := by push_cast; linarith
  have hinv : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 2230 / 1000 * w := by
    have hTR : 46 / 100 / (n : ℝ) ≤ w := by
      rw [hw, div_le_div_iff₀ hn0 hQ0]; nlinarith
    have h4 : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 2230 / 1000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 128
  have htail : √(exp (-(epsW21 20 ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹) ^ 128 ≤
      (36788 / 100000 : ℝ) ^ 111 * (2230 / 1000 * w) ^ 128 :=
    mul_le_mul htl h2' (by positivity) (by positivity)
  -- `w ≤ 1.000016·T/R`
  have hwu : w ≤ 1000026 / 1000000 * (T / R) := by
    rw [hw, div_le_iff₀ hQ0]
    have e : 1000026 / 1000000 * (T / R) * (R - T) = T * (1000026 / 1000000 * (1 - T / R)) := by
      field_simp
    rw [e]
    have hTR : T / R ≤ 528 / 1000 / 21000 := by
      rw [div_le_iff₀ hR0]; nlinarith
    have : 1 ≤ 1000026 / 1000000 * (1 - T / R) := by nlinarith
    nlinarith
  have hfin : w ^ 128 + w ^ 128 * (19713 / 1000) +
      (36788 / 100000 : ℝ) ^ 111 * (2230 / 1000 * w) ^ 128 ≤ w ^ 128 * (207140 / 10000) := by
    have e : (36788 / 100000 : ℝ) ^ 111 * (2230 / 1000 * w) ^ 128 =
        ((36788 / 100000 : ℝ) ^ 111 * (2230 / 1000) ^ 128) * w ^ 128 := by ring
    rw [e]
    have : (36788 / 100000 : ℝ) ^ 111 * (2230 / 1000) ^ 128 ≤ 1 / 1000 := by norm_num
    nlinarith [pow_pos hw0 128]
  have hwf : w ^ 128 * (207140 / 10000) ≤ (10240 / 10000 * (T / R)) ^ 128 := by
    have h1 : w ^ 128 ≤ (1000026 / 1000000 * (T / R)) ^ 128 := pow_le_pow_left₀ hw0.le hwu 128
    have hu0 : 0 ≤ T / R := by positivity
    calc w ^ 128 * (207140 / 10000) ≤ (1000026 / 1000000 * (T / R)) ^ 128 * (207140 / 10000) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((1000026 / 1000000) ^ 128 * (207140 / 10000)) * (T / R) ^ 128 := by ring
      _ ≤ (10240 / 10000) ^ 128 * (T / R) ^ 128 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10240 / 10000 * (T / R)) ^ 128 := by ring
  rw [h0] at h
  push_cast at h htail
  linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms W128_le_21
