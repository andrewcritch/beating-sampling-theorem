import BstLean.Part160Cov8
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Event
import BstLean.Part187R160Cov

/-! Part 187 (file `Part187R160Cov8`): copy of `Part160Cov8` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 jacT nuA jS)
open scoped ENNReal

variable {n : ℕ}

/-- The window form for `1 ≤ q ≤ 4` (`ε = 3/100`):
`W_q ≤ (1.0629·θ/n)^q + 0.001504·(2.1762·θ/n)^q`. -/
theorem WqN_le_theta_gen (hn : 16250 ≤ n) {q : ℕ} (hq4 : q ≤ 4) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN q c τ ≤ (10629 / 10000 * (thetaC c τ / n)) ^ q +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ q := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hqR : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  have h := WqN_le (q := q) (by omega) c hτ (ε := 3 / 100) (by norm_num) (by norm_num)
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
  have hT16 : 16250 * T ≤ 55 / 100 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have e : (n : ℝ) * T / R / n = T / R := by field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 3 / 100) ^ 2 * (R - T)) ≤ 10629 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10629 / 10000 * T * ((1 - 3 / 100) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 q
  -- the second term
  have hexp : exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ 1504 / 10 ^ 6 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1504 / 10 ^ 6 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans exp_neg_13_le)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * q := by linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * q)⁻¹ ≤ 21762 / 10000 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * q)⁻¹ ≤ 21762 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv q
  have h2 : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) * (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q ≤
      1504 / 10 ^ 6 * (21762 / 10000 * (T / R)) ^ q :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  linarith

/-- **`E[(τ²/|y|²)²] ≤ (1.0665·θ/n)²`** for `n ≥ 16250`, `0.46 ≤ θ ≤ 0.55`. -/
theorem W2_le_theta (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 2 c τ ≤ (10665 / 10000 * (thetaC c τ / n)) ^ 2 := by
  have h := WqN_le_theta_gen hn (q := 2) (by norm_num) c hτ hθ0 hθ1
  refine h.trans (le_of_sub_nonneg ?_)
  have e : (10665 / 10000 * (thetaC c τ / n)) ^ 2 - ((10629 / 10000 * (thetaC c τ / n)) ^ 2 +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ 2) =
      ((10665 / 10000 : ℝ) ^ 2 - (10629 / 10000) ^ 2 - 1504 / 10 ^ 6 * (21762 / 10000) ^ 2) *
        (thetaC c τ / n) ^ 2 := by ring
  rw [e]
  exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- **`E[(τ²/|y|²)⁴] ≤ (1.07·θ/n)⁴`** for `n ≥ 16250`, `0.46 ≤ θ ≤ 0.55`. -/
theorem W4_le_theta (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 4 c τ ≤ (107 / 100 * (thetaC c τ / n)) ^ 4 := by
  have h := WqN_le_theta_gen hn (q := 4) (by norm_num) c hτ hθ0 hθ1
  refine h.trans (le_of_sub_nonneg ?_)
  have e : (107 / 100 * (thetaC c τ / n)) ^ 4 - ((10629 / 10000 * (thetaC c τ / n)) ^ 4 +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ 4) =
      ((107 / 100 : ℝ) ^ 4 - (10629 / 10000) ^ 4 - 1504 / 10 ^ 6 * (21762 / 10000) ^ 4) *
        (thetaC c τ / n) ^ 4 := by ring
  rw [e]
  exact mul_nonneg (by norm_num) (by positivity)


/-- The charge of `SXqN n q` when `q·P' = 200`: at most `5·10⁻⁵` (`n ≥ 16250`, `τ > 0`;
`P = 200`, `η = 6/1000`, `jS ≤ 1.0491`). -/
theorem SXqN_charge (hn : 16250 ≤ n) {q P' : ℕ} (hq : q ≤ 4) (hP : 1 ≤ P')
    (hqP : q * P' = 200) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXqN n q} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXqN n q} =
      {θ | (1157 / 1000 * (n : ℝ)) ^ q * WqN q c τ < XqN q θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN q θ.1 θ.2 c τ ≤ (1157 / 1000 * (n : ℝ)) ^ q * WqN q c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := q) (P' := P') hP (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => by
      rw [hqP]
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  rw [hqP]
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.R.jS_200_le_16250 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10491 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 9513 / 10000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part160.R.pow_9513_le

/-- **The charge of `SXi4n`**: at most `5·10⁻⁵` (`n ≥ 16250`, `τ > 0`). -/
theorem SXi4n_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi4n n} ≤ 5 / 100000 :=
  SXqN_charge hn (q := 2) (P' := 100) (by norm_num) (by norm_num) (by norm_num) c τ hτ

/-- **The charge of `SXi8n`**: at most `5·10⁻⁵` (`n ≥ 16250`, `τ > 0`). -/
theorem SXi8n_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi8n n} ≤ 5 / 100000 :=
  SXqN_charge hn (q := 4) (P' := 50) (by norm_num) (by norm_num) (by norm_num) c τ hτ


end BstLean.Part160.R

