import BstLean.Part160Cov
import BstLean.Part187R143HidC
import BstLean.Part187R143HidC2
import BstLean.Part187R153PPs4
import BstLean.Part187R153Final
import BstLean.Part187R154C16
import BstLean.Part187R154NumA16
import BstLean.Part187R154NumB16
import BstLean.Part187R154Num16
import BstLean.Part187R160Event

/-! Part 187 (file `Part187R160Cov`): copy of `Part160Cov` re-proved at the floor `16250 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS jacT nuA jS)
open scoped ENNReal

variable {n : ℕ}

set_option exponentiation.threshold 1000 in
/-- `0.9513²⁰⁰ ≤ 5·10⁻⁵` (for the floor `16250`). -/
lemma pow_9513_le : (9513 / 10000 : ℝ) ^ 200 ≤ 5 / 100000 := by norm_num

/-- **`E[τ²/|y|²] ≤ 1.067·θ/n`** for `n ≥ 16250` and `0.46 ≤ θ ≤ 0.55` (`ε = 3/100`). The paper
has `(θ/n)/(1 − 4θ/n)` by the Poisson mixture of central chi-square distributions. -/
theorem Winv_le_theta (hn : 16250 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    Winv c τ ≤ 1067 / 1000 * (thetaC c τ / n) := by
  have hnR : (16250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := Winv_le (by omega : 6 ≤ n) c hτ (ε := 3 / 100) (by norm_num) (by norm_num)
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
  -- the first term
  have h1 : T / ((1 - 3 / 100) ^ 2 * (R - T)) ≤ 10629 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10629 / 10000 * T * ((1 - 3 / 100) ^ 2 * (R - T)) := by ring
  -- the second term
  have hn5 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have hexp : exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hI : 1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)) ≤ 1 / (((n : ℝ) - 5) ^ 2) := by
    apply one_div_le_one_div_of_le (pow_pos hn5 2)
    nlinarith
  have h2 : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) *
      (1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)))) ≤ 1504 / 10 ^ 6 / ((n : ℝ) - 5) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1504 / 10 ^ 6 / ((n : ℝ) - 5) by positivity)]
    apply Real.sqrt_le_sqrt
    have e : (1504 / 10 ^ 6 / ((n : ℝ) - 5)) ^ 2 =
        (1504 / 10 ^ 6 : ℝ) ^ 2 * (1 / (((n : ℝ) - 5) ^ 2)) := by
      field_simp
    rw [e]
    exact mul_le_mul (hexp.trans exp_neg_13_le) hI (by positivity) (by positivity)
  have h3 : 1504 / 10 ^ 6 / ((n : ℝ) - 5) ≤ 33 / 10000 * (T / R) := by
    have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
      rw [div_le_div_iff₀ hn0 hR0]
      linarith
    have h4 : 1504 / 10 ^ 6 / ((n : ℝ) - 5) ≤ 33 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hn5 hn0]
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have e : 1067 / 1000 * ((n : ℝ) * T / R / n) = 1067 / 1000 * (T / R) := by
    field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  linarith


/-- **The charge of the event**: for `n ≥ 16250` and `τ > 0`,
`Pr(Ξ > 1.157·γ_A·W) ≤ 5·10⁻⁵` (`P = 200`, `η = 6/1000`, `jS ≤ 1.0488`). -/
theorem SXi_charge (hn : 16250 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXi n} =
      {θ | 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ < XiS θ.1 θ.2 c τ} := by
    ext θ
    show ¬ (XiS θ.1 θ.2 c τ ≤ 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XiS_w (n := n) (P := 200) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.R.jS_200_le_16250 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10491 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 9513 / 10000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans pow_9513_le

end BstLean.Part160.R

