import BstLean.Part80Defs
import BstLean.Part69Final

/-!
# Part 80: the cost clause at `ε = 1/2`, surrogate accuracy `e80 = 1/2` (`etaQ = 1/40`), `n ≥ 3000`
-/

namespace BstLean.Part80

open BstLean.Part41 (Pn NN baseline)
open BstLean.Part56 (KRK costLine56)
open BstLean.Part69 (K_le69 Pn2_69 NN2_69)

/-- The surrogate accuracy parameter of Part 80: `etaQ e80 = 1/40`. -/
noncomputable def e80 : ℝ := 1 / 2

theorem etaQ_e80 : BstLean.Part43.etaQ e80 = 1 / 40 := by
  unfold BstLean.Part43.etaQ BstLean.Part43.xi43 e80
  rw [min_eq_left (by norm_num)]; norm_num

theorem Leta_e80 : BstLean.Part43.Leta e80 = Real.log 41 := by
  unfold BstLean.Part43.Leta
  rw [etaQ_e80]; norm_num

theorem Leta_e80_nonneg : 0 ≤ BstLean.Part43.Leta e80 := by
  rw [Leta_e80]; exact Real.log_nonneg (by norm_num)

theorem Leta_e80_lt : BstLean.Part43.Leta e80 < 4 := by
  rw [Leta_e80, Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have h4 : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [← h4]
  have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  calc (41 : ℝ) < 2.7 ^ 4 := by norm_num
    _ ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) h27 4

/-- `K = KRK 1 n e80 ≤ 9 n + 6`. -/
theorem K80_le (n : ℕ) : (KRK 1 n e80 : ℝ) ≤ 9 * (n : ℝ) + 6 := by
  have h := K_le69 (1 * n) e80
  have h0 := Leta_e80_nonneg
  have h4 := Leta_e80_lt
  rw [one_mul, Nat.abs_cast, abs_of_nonneg h0] at h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (1 + 2 * BstLean.Part43.Leta e80) * (n : ℝ) ≤ 9 * n :=
    mul_le_mul_of_nonneg_right (by linarith) hn0
  have hL2 : BstLean.Part43.Leta e80 ^ 2 ≤ 16 := by nlinarith
  unfold KRK
  rw [one_mul]
  linarith

/-- **The cost clause of Part 80**: for `n ≥ 3000`, a moment program of cost
`≤ 11 n + 23 K + 194` and a line program of cost `≤ costLine56 n 2 2` together cost less than the
sampling baseline at `ε = 1/2`. -/
theorem cost80 (n : ℕ) (hn : 3000 ≤ n) (pmc pgc : ℕ)
    (hpm : (pmc : ℝ) ≤ 11 * n + 23 * (KRK 1 n e80) + 194)
    (hpg : (pgc : ℝ) ≤ costLine56 n 2 2) :
    (pmc : ℝ) + pgc < baseline n 2 (1 / 2) := by
  have hn' : (3000 : ℝ) ≤ n := by exact_mod_cast hn
  have hK := K80_le n
  have hbase : 91 / 100 * Pn n 2 / (1 / 2) ^ 2 ≤ baseline n 2 (1 / 2) := le_max_right _ _
  have hcl : (pgc : ℝ) ≤ 2 * Pn n 2 + 3 * NN n 2 + 2304 * ((n : ℝ) + 1) ^ 2 := by
    refine hpg.trans (le_of_eq ?_)
    unfold costLine56; norm_num
  rw [Pn2_69] at hbase hcl
  rw [NN2_69 n (by omega)] at hcl
  set N := (n : ℝ)
  have h1 : 0 ≤ N - 3000 := by linarith
  have h2 : 0 ≤ (N - 3000) ^ 2 := by positivity
  have h3 : 0 ≤ (N - 3000) ^ 3 := by positivity
  have e2 : (N - 3000) ^ 2 = N ^ 2 - 6000 * N + 9000000 := by ring
  have e3 : (N - 3000) ^ 3 = N ^ 3 - 9000 * N ^ 2 + 27000000 * N - 27000000000 := by ring
  rw [e2] at h2
  rw [e3] at h3
  have key : (11 * N + 23 * (9 * N + 6) + 194)
      + (2 * (N * (N + 1) * (N + 2) / 2) + 3 * ((N + 1) * (N + 2) / 2) + 2304 * (N + 1) ^ 2)
      < 91 / 100 * (N * (N + 1) * (N + 2) / 2) / (1 / 2) ^ 2 := by
    have e : 91 / 100 * (N * (N + 1) * (N + 2) / 2) / (1 / 2) ^ 2 -
        ((11 * N + 23 * (9 * N + 6) + 194)
          + (2 * (N * (N + 1) * (N + 2) / 2) + 3 * ((N + 1) * (N + 2) / 2) + 2304 * (N + 1) ^ 2))
        = 82 / 100 * N ^ 3 - 230304 / 100 * N ^ 2 - 482886 / 100 * N - 2639 := by ring
    linarith
  linarith

end BstLean.Part80

#print axioms BstLean.Part80.cost80
