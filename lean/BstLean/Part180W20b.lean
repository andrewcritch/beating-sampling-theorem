import BstLean.Part176All

/-!
# Part 180 (file `W20b`): the layered bound of the radius moment `W₂₀` at `n ≥ 23 000`

No proof is left open; no `native_decide` or `axiom` is used.

Part 176's `WqN_le_layer` with the ten levels `ε_k = 0.0042·min(k, 10)` (a copy of Part 178's
file `W20b` at `n ≥ 23 000`):
**`W20_le_23`**: `E[(τ²/|y|²)²⁰] ≤ (1.0177·θ/n)²⁰` for `n ≥ 23 000`, `0.46 ≤ θ ≤ 0.528`.
The docstrings of the copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part180

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part160 (WqN)
open BstLean.Part176 (fL fL_mono fL_eq WqN_le_layer exp_neg_quart')

variable {n : ℕ}

/-- The levels `ε_k = 0.0036·min(k, 10)`. -/
noncomputable def eps23 (k : ℕ) : ℝ := 43 / 10000 * ((min k 10 : ℕ) : ℝ)

lemma eps23_mono (k : ℕ) : eps23 k ≤ eps23 (k + 1) := by
  unfold eps23
  have : ((min k 10 : ℕ) : ℝ) ≤ ((min (k + 1) 10 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 10 (Nat.le_succ k)
  linarith

lemma eps23_lt (k : ℕ) : eps23 k < 1 := by
  unfold eps23
  have : ((min k 10 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast min_le_right k 10
  linarith

/-- `C(e) = ((1 − e)²)^{−20}`. -/
lemma fL_eq {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 20 τ Q e = (τ ^ 2 / Q) ^ 20 * (1 / ((1 - e) ^ 2) ^ 20) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 20 = (1 / (1 - e) ^ 2) ^ 20 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp


/-- `C(e) = ((1 − e)²)^{−20}`. -/
noncomputable def C23 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 20

/-- The tail bound `P(e) = (1 + x/4 + (x/4)²/2)^{−4}` at `x = 32 196·e²`. -/
noncomputable def P23 (e : ℝ) : ℝ := 1 / (1 + e ^ 2 * 21779 / 4 + (e ^ 2 * 21779 / 4) ^ 2 / 2) ^ 4

lemma sum23_le : ∑ k ∈ Finset.range 10, (C23 (eps23 (k + 1)) - C23 (eps23 k)) * P23 (eps23 k) ≤
    40680 / 100000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eps23, C23, P23]
  norm_num


open BstLean.Part150 (thetaC rhoC) in
/-- **`E[(τ²/|y|²)²⁰] ≤ (1.0146·θ/n)²⁰`** for `n ≥ 34 000`, `0.46 ≤ θ ≤ 0.528` (the layered bound
with the ten levels `ε_k = 0.0036k`). -/
theorem W20_le_23 (hn : 23000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10177 / 10000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le_layer (q := 20) (by omega) c hτ eps23 10 (by unfold eps23; norm_num)
    eps23_mono eps23_lt
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1 ⊢
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [show normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 = R - T by rw [hR, hT]] at h
  rw [← hT] at h
  have hT45 : 23000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  set w := T / (R - T) with hw
  have hw0 : 0 < w := div_pos hT0 hQ0
  -- `Q/(2T) ≥ 42 613`
  have hlam : 21779 ≤ (R - T) / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : ∀ k, exp (-(eps23 k ^ 2 * (R - T)) / (2 * T)) ≤ P23 (eps23 k) := by
    intro k
    rw [neg_div]
    refine exp_neg_quart' (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hfL : ∀ k, fL 20 τ (R - T) (eps23 k) = w ^ 20 * C23 (eps23 k) := fun k => by
    rw [fL_eq hQ0 (eps23_lt k), C23, hw, ← hT]
  have hsum : ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (eps23 (k + 1)) - fL 20 τ (R - T) (eps23 k)) *
      exp (-(eps23 k ^ 2 * (R - T)) / (2 * T)) ≤ w ^ 20 * (40680 / 100000) := by
    calc _ ≤ ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (eps23 (k + 1)) - fL 20 τ (R - T) (eps23 k)) *
          P23 (eps23 k) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hE k)
              (by linarith [fL_mono (q := 20) (τ := τ) hQ0 (eps23_mono k) (eps23_lt (k + 1))])
      _ = w ^ 20 * ∑ k ∈ Finset.range 10, (C23 (eps23 (k + 1)) - C23 (eps23 k)) * P23 (eps23 k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hfL, hfL]; ring
      _ ≤ w ^ 20 * (40680 / 100000) := mul_le_mul_of_nonneg_left sum23_le (by positivity)
  have h0 : fL 20 τ (R - T) (eps23 0) = w ^ 20 := by
    rw [hfL]; unfold C23 eps23; norm_num
  -- the tail
  have he10 : eps23 10 = 43 / 1000 := by unfold eps23; norm_num
  have htl : √(exp (-(eps23 10 ^ 2 * (R - T)) / (2 * T))) ≤ (36788 / 100000) ^ 20 := by
    have h40 : exp (-(eps23 10 ^ 2 * (R - T)) / (2 * T)) ≤ exp (-1) ^ 40 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [he10, neg_div, mul_div_assoc]
      have : (40 : ℝ) ≤ (43 / 1000) ^ 2 * ((R - T) / (2 * T)) := by nlinarith
      push_cast; linarith
    have h1 : exp (-1) ≤ 36788 / 100000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : exp (-1) ^ 40 ≤ ((36788 / 100000 : ℝ) ^ 20) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (exp_pos _).le h1 _
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (36788 / 100000) ^ 20 by positivity)]
    exact Real.sqrt_le_sqrt (h40.trans h2)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21820 / 10000 * w := by
    have hTR : 46 / 100 / (n : ℝ) ≤ w := by
      rw [hw, div_le_div_iff₀ hn0 hQ0]; nlinarith
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21820 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have htail : √(exp (-(eps23 10 ^ 2 * (R - T)) / (2 * T))) * (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (36788 / 100000 : ℝ) ^ 20 * (21820 / 10000 * w) ^ 20 :=
    mul_le_mul htl h2' (by positivity) (by positivity)
  -- `w ≤ 1.0000118·T/R`
  have hwu : w ≤ 1000024 / 1000000 * (T / R) := by
    rw [hw, div_le_iff₀ hQ0]
    have e : 1000024 / 1000000 * (T / R) * (R - T) = T * (1000024 / 1000000 * (1 - T / R)) := by
      field_simp
    rw [e]
    have hTR : T / R ≤ 528 / 1000 / 23000 := by
      rw [div_le_iff₀ hR0]; nlinarith
    have : 1 ≤ 1000024 / 1000000 * (1 - T / R) := by nlinarith
    nlinarith
  have hfin : w ^ 20 + w ^ 20 * (40680 / 100000) + (36788 / 100000 : ℝ) ^ 20 * (21820 / 10000 * w) ^ 20 ≤
      w ^ 20 * (14192 / 10000) := by
    have e : (36788 / 100000 : ℝ) ^ 20 * (21820 / 10000 * w) ^ 20 =
        ((36788 / 100000 : ℝ) ^ 20 * (21820 / 10000) ^ 20) * w ^ 20 := by ring
    rw [e]
    have : (36788 / 100000 : ℝ) ^ 20 * (21820 / 10000) ^ 20 ≤ 124 / 10000 := by norm_num
    nlinarith [pow_pos hw0 20]
  have hwf : w ^ 20 * (14192 / 10000) ≤ (10177 / 10000 * ((n : ℝ) * T / R / n)) ^ 20 := by
    have e : (n : ℝ) * T / R / n = T / R := by field_simp
    rw [e]
    have h1 : w ^ 20 ≤ (1000024 / 1000000 * (T / R)) ^ 20 := pow_le_pow_left₀ hw0.le hwu 20
    have hu0 : 0 ≤ T / R := by positivity
    calc w ^ 20 * (14192 / 10000) ≤ (1000024 / 1000000 * (T / R)) ^ 20 * (14192 / 10000) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((1000024 / 1000000) ^ 20 * (14192 / 10000)) * (T / R) ^ 20 := by ring
      _ ≤ (10177 / 10000) ^ 20 * (T / R) ^ 20 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10177 / 10000 * (T / R)) ^ 20 := by ring
  rw [h0] at h
  push_cast at h htail
  linarith

end BstLean.Part180
