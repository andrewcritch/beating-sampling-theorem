import BstLean.Part176All

/-!
# Part 181 (file `W128`): the layered bound of the radius moment `W₁₂₈` at `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 180's file `W128b` at `n ≥ 22 000`: Part 176's `WqN_le_layer` at `q = 128` with
the twenty levels `ε_k = 0.0053·min(k, 20)`:
**`W128_le_22`**: `E[(τ²/|c' + τξ|²)¹²⁸] ≤ (1.0233·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 22 000`,
`0.46 ≤ θ ≤ 0.528` and every `c'` with `|c'| = |c|`.
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part160 (WqN)
open BstLean.Part176 (fL fL_mono WqN_le_layer exp_neg_quart')

variable {n : ℕ}

/-- The levels `ε_k = 0.0042·min(k, 20)`. -/
noncomputable def epsW22 (k : ℕ) : ℝ := 53 / 10000 * ((min k 20 : ℕ) : ℝ)

lemma epsW22_mono (k : ℕ) : epsW22 k ≤ epsW22 (k + 1) := by
  unfold epsW22
  have : ((min k 20 : ℕ) : ℝ) ≤ ((min (k + 1) 20 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 20 (Nat.le_succ k)
  linarith

lemma epsW22_lt (k : ℕ) : epsW22 k < 1 := by
  unfold epsW22
  have : ((min k 20 : ℕ) : ℝ) ≤ 20 := by exact_mod_cast min_le_right k 20
  linarith

/-- `fL 128 τ Q e = (τ²/Q)¹²⁸·((1 − e)²)^{−128}`. -/
lemma fL_eqW22 {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 128 τ Q e = (τ ^ 2 / Q) ^ 128 * (1 / ((1 - e) ^ 2) ^ 128) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 128 = (1 / (1 - e) ^ 2) ^ 128 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp

/-- `C(e) = ((1 − e)²)^{−128}`. -/
noncomputable def CW22 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 128

/-- The tail bound `P(e) = (1 + x/4 + (x/4)²/2)^{−4}` at `x = 32 196·e²`. -/
noncomputable def PW22 (e : ℝ) : ℝ :=
  1 / (1 + e ^ 2 * 20832 / 4 + (e ^ 2 * 20832 / 4) ^ 2 / 2) ^ 4

lemma sumW22_le : ∑ k ∈ Finset.range 20, (CW22 (epsW22 (k + 1)) - CW22 (epsW22 k)) * PW22 (epsW22 k) ≤
    17787 / 1000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, epsW22, CW22, PW22]
  norm_num

/-- **`E[(τ²/|c' + τξ|²)¹²⁸] ≤ (1.0172·τ²/(|c|² + nτ²))¹²⁸`** for `n ≥ 34 000`,
`0.46 ≤ θ ≤ 0.528`, `|c'| = |c|` (the layered bound with twenty levels `ε_k = 0.0042k`). -/
theorem W128_le_22 (hn : 22000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ)
    (hθ1 : BstLean.Part150.thetaC c τ ≤ 528 / 1000) :
    WqN 128 c' τ ≤ (10233 / 10000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 := by
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le_layer (q := 128) (by omega) c' hτ epsW22 20 (by unfold epsW22; norm_num)
    epsW22_mono epsW22_lt
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
  have hT45 : 22000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  set w := T / (R - T) with hw
  have hw0 : 0 < w := div_pos hT0 hQ0
  have hlam : 20832 ≤ (R - T) / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : ∀ k, exp (-(epsW22 k ^ 2 * (R - T)) / (2 * T)) ≤ PW22 (epsW22 k) := by
    intro k
    rw [neg_div]
    refine exp_neg_quart' (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hfL : ∀ k, fL 128 τ (R - T) (epsW22 k) = w ^ 128 * CW22 (epsW22 k) := fun k => by
    rw [fL_eqW22 hQ0 (epsW22_lt k), CW22, hw, ← hT]
  have hsum : ∑ k ∈ Finset.range 20, (fL 128 τ (R - T) (epsW22 (k + 1)) -
      fL 128 τ (R - T) (epsW22 k)) * exp (-(epsW22 k ^ 2 * (R - T)) / (2 * T)) ≤
      w ^ 128 * (17787 / 1000) := by
    calc _ ≤ ∑ k ∈ Finset.range 20, (fL 128 τ (R - T) (epsW22 (k + 1)) -
          fL 128 τ (R - T) (epsW22 k)) * PW22 (epsW22 k) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hE k)
              (by linarith [fL_mono (q := 128) (τ := τ) hQ0 (epsW22_mono k) (epsW22_lt (k + 1))])
      _ = w ^ 128 * ∑ k ∈ Finset.range 20, (CW22 (epsW22 (k + 1)) - CW22 (epsW22 k)) * PW22 (epsW22 k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hfL, hfL]; ring
      _ ≤ w ^ 128 * (17787 / 1000) := mul_le_mul_of_nonneg_left sumW22_le (by positivity)
  have h0 : fL 128 τ (R - T) (epsW22 0) = w ^ 128 := by
    rw [hfL]; unfold CW22 epsW22; norm_num
  -- the tail
  have he20 : epsW22 20 = 106 / 1000 := by unfold epsW22; norm_num
  have htl : √(exp (-(epsW22 20 ^ 2 * (R - T)) / (2 * T))) ≤ (36788 / 100000) ^ 113 := by
    have h40 : exp (-(epsW22 20 ^ 2 * (R - T)) / (2 * T)) ≤ exp (-1) ^ 226 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [he20, neg_div, mul_div_assoc]
      have : (226 : ℝ) ≤ (106 / 1000) ^ 2 * ((R - T) / (2 * T)) := by nlinarith
      push_cast; linarith
    have h1 : exp (-1) ≤ 36788 / 100000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : exp (-1) ^ 226 ≤ ((36788 / 100000 : ℝ) ^ 113) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (exp_pos _).le h1 _
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (36788 / 100000) ^ 113 by positivity)]
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
  have htail : √(exp (-(epsW22 20 ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹) ^ 128 ≤
      (36788 / 100000 : ℝ) ^ 113 * (2230 / 1000 * w) ^ 128 :=
    mul_le_mul htl h2' (by positivity) (by positivity)
  -- `w ≤ 1.000016·T/R`
  have hwu : w ≤ 1000025 / 1000000 * (T / R) := by
    rw [hw, div_le_iff₀ hQ0]
    have e : 1000025 / 1000000 * (T / R) * (R - T) = T * (1000025 / 1000000 * (1 - T / R)) := by
      field_simp
    rw [e]
    have hTR : T / R ≤ 528 / 1000 / 22000 := by
      rw [div_le_iff₀ hR0]; nlinarith
    have : 1 ≤ 1000025 / 1000000 * (1 - T / R) := by nlinarith
    nlinarith
  have hfin : w ^ 128 + w ^ 128 * (17787 / 1000) +
      (36788 / 100000 : ℝ) ^ 113 * (2230 / 1000 * w) ^ 128 ≤ w ^ 128 * (187871 / 10000) := by
    have e : (36788 / 100000 : ℝ) ^ 113 * (2230 / 1000 * w) ^ 128 =
        ((36788 / 100000 : ℝ) ^ 113 * (2230 / 1000) ^ 128) * w ^ 128 := by ring
    rw [e]
    have : (36788 / 100000 : ℝ) ^ 113 * (2230 / 1000) ^ 128 ≤ 1 / 10000 := by norm_num
    nlinarith [pow_pos hw0 128]
  have hwf : w ^ 128 * (187871 / 10000) ≤ (10233 / 10000 * (T / R)) ^ 128 := by
    have h1 : w ^ 128 ≤ (1000025 / 1000000 * (T / R)) ^ 128 := pow_le_pow_left₀ hw0.le hwu 128
    have hu0 : 0 ≤ T / R := by positivity
    calc w ^ 128 * (187871 / 10000) ≤ (1000025 / 1000000 * (T / R)) ^ 128 * (187871 / 10000) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((1000025 / 1000000) ^ 128 * (187871 / 10000)) * (T / R) ^ 128 := by ring
      _ ≤ (10233 / 10000) ^ 128 * (T / R) ^ 128 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10233 / 10000 * (T / R)) ^ 128 := by ring
  rw [h0] at h
  push_cast at h htail
  linarith

end BstLean.Part181
