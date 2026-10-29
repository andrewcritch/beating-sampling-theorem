import BstLean.Part165Sig

/-!
# Part 165 (file `Ev`): the Agent event of the gradient moment of order 40

No proof is left open; no `native_decide` or `axiom` is used.

`W_q = E_ξ(τ²/|y|²)^q`, `X_q = E_ξ[(τ²/|y|²)^q ‖𝒥Π‖^{2q}]` (Part 160 `Cov8`). The event is
Part 160's `SXqN n 20`: `X₂₀ ≤ (1.157·n)²⁰·W₂₀`.

* `W20_le_theta`: `W₂₀ ≤ (1.109·θ/n)²⁰` (`n ≥ 23 000`, `0.46 ≤ θ ≤ 0.55`; `ε = 5/100` in
  Part 160's `WqN_le`).
* **`SX20_charge`**: `Pr((A₁, A₂) ∉ SXqN n 20) ≤ 5·10⁻⁵` for every `(ĉ, τ)`, `τ > 0`,
  `n ≥ 16 384` (Markov over the weights at order `400`, Lemma PP; `q·P' = 20·10 = 200`).
* **`tX20_le`**: on the event and in the window, `t_A²⁰·X₂₀ ≤ (0.706·γ_A/n)²⁰`.
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nuA jS)
open BstLean.Part160 (WqN XqN SXqN AgFam markov_XqN WqN_le exp_neg_13_le)

variable {n : ℕ}

/-- **`E[(τ²/|y|²)²⁰] ≤ (1.109·θ/n)²⁰`** for `n ≥ 23 000`, `0.46 ≤ θ ≤ 0.55`. -/
theorem W20_le_theta (hn : 23000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 20 c τ ≤ (1109 / 1000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 20) (by omega) c hτ (ε := 5 / 100) (by norm_num) (by norm_num)
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
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hT23 : 23000 * T ≤ 55 / 100 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have e : (n : ℝ) * T / R / n = T / R := by field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 5 / 100) ^ 2 * (R - T)) ≤ 11081 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 11081 / 10000 * ((1 - 5 / 100) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (11081 / 10000 * ((1 - 5 / 100) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 11081 / 10000 * T * ((1 - 5 / 100) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 20
  -- the second term
  have hexp : exp (-((5 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) ^ 4 := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hE4 : exp (-13) ^ 4 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 4) ^ 2 := by
    have := pow_le_pow_left₀ (exp_pos _).le exp_neg_13_le 4
    calc exp (-13) ^ 4 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 2) ^ 4 := this
      _ = ((1504 / 10 ^ 6 : ℝ) ^ 4) ^ 2 := by ring
  have hsq : √(exp (-((5 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ (1504 / 10 ^ 6 : ℝ) ^ 4 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (1504 / 10 ^ 6) ^ 4 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans hE4)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have h2 : √(exp (-((5 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (1504 / 10 ^ 6 : ℝ) ^ 4 * (219 / 100 * (T / R)) ^ 20 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (11081 / 10000 * (T / R)) ^ 20 + (1504 / 10 ^ 6 : ℝ) ^ 4 * (219 / 100 * (T / R)) ^ 20 ≤
      (1109 / 1000 * (T / R)) ^ 20 := by
    have e2 : (1109 / 1000 * (T / R)) ^ 20 - ((11081 / 10000 * (T / R)) ^ 20 +
        (1504 / 10 ^ 6 : ℝ) ^ 4 * (219 / 100 * (T / R)) ^ 20) =
        ((1109 / 1000 : ℝ) ^ 20 - (11081 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 4 * (219 / 100) ^ 20) *
          (T / R) ^ 20 := by ring
    have : 0 ≤ ((1109 / 1000 : ℝ) ^ 20 - (11081 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 4 * (219 / 100) ^ 20) *
          (T / R) ^ 20 := mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith

/-- **The charge of `SXqN n 20`**: at most `5·10⁻⁵` (`n ≥ 16384`, `τ > 0`; `P' = 10`, so the
weight moment has order `2·20·10 = 400`, as in Part 160). -/
theorem SX20_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXqN n 20} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXqN n 20} =
      {θ | (1157 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 10) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.jS_200_le_16384 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10488 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 951 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part153.pow_951_le

/-- **The gradient moment of order 40 on the event**: `t_A²⁰·X₂₀ ≤ (0.706·γ_A/n)²⁰`
(`1.157·1.109·0.55 ≤ 0.706`), for `n ≥ 23 000` and `0.46 ≤ θ_in ≤ 0.55`. -/
theorem tX20_le (hn : 23000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXqN n 20) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (706 / 1000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_theta hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (1157 / 1000 * (1109 / 1000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 1157 / 1000 * (1109 / 1000) * thetaC c τ ≤ 706 / 1000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (706 / 1000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (706 / 1000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp

end BstLean.Part165
