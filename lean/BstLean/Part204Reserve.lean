import BstLean.Part204Scalar

/-! S06: scalar bounds for any positive hidden reserve. -/

namespace BstLean.Part204

open Real
open BstLean.Part130 BstLean.Part134 BstLean.Part159 BstLean.Part157
open BstLean.Part140 (kap1 kap1_window)

variable {n : ℕ}

/-- The scalar bound uses a variable hidden reserve, without a narrow-window premise. -/
theorem pap_q_reserve (hn : 4096 ≤ n) {θ : WHid n} {ε : ℝ}
    (hε : ε < 1) (hS : |SWp θ / 2 - 1| ≤ ε) :
    0 ≤ qOf n (ccP n) θ ∧
      qOf n (ccP n) θ ≤
        √(2 * (4938 / 10000 : ℝ) ^ 2 /
          (2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2)) ∧
      |qOf n (ccP n) θ - 1| ≤
        (198 / 100 * |kapT n - kap1 (2 * n)| + 4878 / 10000 * ε) /
          (2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2) := by
  have hεnonneg : 0 ≤ ε := (abs_nonneg _).trans hS
  have hn4 : 4096 ≤ n := by omega
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨-, hκ1, hκ2⟩ := BstLean.Part204.kapT_window hn (BstLean.Part201.constK hn)
  obtain ⟨hk1, hk2⟩ := kap1_window hn4
  have hS' : |SWp θ / 2 - 1| ≤ ε := hS
  obtain ⟨hSa, hSb⟩ := abs_le.mp hS'
  have hS1 : 2 * (1 - ε) ≤ SWp θ := by linarith
  have hS2 : SWp θ ≤ 2 * (1 + ε) := by linarith
  have hκ0 : 0 < kapT n := by linarith
  have hk0 : 0 < kap1 (2 * n) := by linarith
  have hSpos : 0 < SWp θ := by linarith
  have hSκ : 0 < SWp θ * kapT n ^ 2 := by positivity
  have hκsq1 : (493719 / 1000000 : ℝ) ^ 2 ≤ kapT n ^ 2 := pow_le_pow_left₀ (by norm_num) hκ1 2
  have hSκ1 : 2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2 ≤ SWp θ * kapT n ^ 2 :=
    mul_le_mul hS1 hκsq1 (by positivity) (by linarith)
  set q := qOf n (ccP n) θ with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 2 * kap1 (2 * n) ^ 2 / (SWp θ * kapT n ^ 2) := by
    rw [hq]
    unfold qOf
    rw [Real.sq_sqrt (by unfold ccP; positivity), hNcast]
    unfold ccP
    field_simp
  -- `q² − 1`
  have hnum : |2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2| ≤
      198 / 100 * |kapT n - kap1 (2 * n)| + 4878 / 10000 * |SWp θ / 2 - 1| := by
    have e : 2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2 =
        -(2 * (kapT n - kap1 (2 * n)) * (kapT n + kap1 (2 * n))) +
          -(2 * (SWp θ / 2 - 1) * kapT n ^ 2) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul]
    have a1 : |kapT n + kap1 (2 * n)| ≤ 99 / 100 := by
      rw [abs_of_pos (by linarith)]
      linarith
    have a2 : |kapT n ^ 2| ≤ 2439 / 10000 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := pow_le_pow_left₀ hκ0.le hκ2 2
      nlinarith
    have a3 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
    rw [a3]
    have b1 : 2 * |kapT n - kap1 (2 * n)| * |kapT n + kap1 (2 * n)| ≤
        2 * |kapT n - kap1 (2 * n)| * (99 / 100) :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    have b2 : 2 * |SWp θ / 2 - 1| * |kapT n ^ 2| ≤ 2 * |SWp θ / 2 - 1| * (2439 / 10000) :=
      mul_le_mul_of_nonneg_left a2 (by positivity)
    linarith
  have hDpos : 0 < 2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2 := by positivity
  have hq1 : |q - 1| ≤ |q ^ 2 - 1| := by
    have e : q ^ 2 - 1 = (q - 1) * (q + 1) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : 0 < q + 1)]
    nlinarith [abs_nonneg (q - 1)]
  refine ⟨hq0, ?_, hq1.trans ?_⟩
  · have hsq : q ^ 2 ≤ 2 * (4938 / 10000 : ℝ) ^ 2 /
        (2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2) := by
      rw [hq2]
      exact div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0.le hk2 2) (by norm_num))
        hDpos hSκ1
    have hr : 0 ≤ 2 * (4938 / 10000 : ℝ) ^ 2 /
        (2 * (1 - ε) * (493719 / 1000000 : ℝ) ^ 2) := by positivity
    exact (Real.le_sqrt hq0 hr).mpr hsq
  · have e : q ^ 2 - 1 =
        (2 * kap1 (2 * n) ^ 2 - SWp θ * kapT n ^ 2) / (SWp θ * kapT n ^ 2) := by
      rw [hq2]
      field_simp
    rw [e, abs_div, abs_of_pos hSκ]
    exact div_le_div₀ (by positivity)
      (hnum.trans (by linarith))
      hDpos hSκ1

end BstLean.Part204

#print axioms BstLean.Part204.pap_q_reserve
