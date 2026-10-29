import BstLean.Part56Low_Transport

namespace BstLean.Part56.LowMoment

open MeasureTheory BstLean.Part29 BstLean.Part41

lemma angular_moment_uniform (k : ℕ) (C : ℝ) :
    ∃ (a : ℝ) (n0 : ℕ), 0 < a ∧ 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v →
        ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
          a ≤ ∫ x, (1 - (∑ i, x i * v i) ^ 2) ^ k ∂lawRK n t v := by
  obtain ⟨N, hN⟩ := exists_nat_gt C
  let L := Real.exp (2 * (C + 1))
  have hL : 0 < L := Real.exp_pos _
  let θ := (4 * L + 1)⁻¹
  have hθ : 0 < θ := by dsimp only [θ]; positivity
  refine ⟨θ ^ k / 2, N + 3, by positivity, by omega, ?_⟩
  intro n hn v hv t ht htC
  cases n with
  | zero => omega
  | succ m =>
    have hq : (Real.sqrt (1 + 2 * L))⁻¹ ≤ Real.exp (-(C + 1)) := by
      have he : L = Real.exp (C + 1) ^ 2 := by
        dsimp only [L]
        rw [show 2 * (C + 1) = (C + 1) + (C + 1) by ring, Real.exp_add, pow_two]
      have hs : Real.exp (C + 1) ≤ Real.sqrt (1 + 2 * L) := by
        calc
          _ = Real.sqrt (Real.exp (C + 1) ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ _ := Real.sqrt_le_sqrt (by rw [← he]; linarith [hL])
      rw [Real.exp_neg]
      exact inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity)) (Real.exp_pos _) |>.mpr hs
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (Real.sqrt (1 + 2 * L))⁻¹) hq m
    have htail : Real.exp (C * (m + 1)) * Real.sqrt 2 *
        ((Real.sqrt (1 + 2 * L))⁻¹) ^ m ≤ 1 / 2 := by
      calc
        _ ≤ Real.exp (C * (m + 1)) * Real.sqrt 2 * (Real.exp (-(C + 1))) ^ m :=
          mul_le_mul_of_nonneg_left hp (by positivity)
        _ = Real.sqrt 2 * Real.exp (C - m) := by
          rw [← Real.exp_nat_mul]
          calc
            _ = Real.sqrt 2 * (Real.exp (C * (m + 1)) * Real.exp ((m : ℝ) * -(C + 1))) := by ring
            _ = _ := by rw [← Real.exp_add]; congr 2; ring
        _ ≤ Real.sqrt 2 * Real.exp (-2) := by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.sqrt_nonneg _)
          have hm : (N : ℝ) + 2 ≤ m := by exact_mod_cast (show N + 2 ≤ m by omega)
          linarith
        _ ≤ 1 / 2 := by
          have he : 3 ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
          have hs : Real.sqrt 2 ≤ 3 / 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
          rw [Real.exp_neg, ← div_eq_mul_inv]
          apply (div_le_iff₀ (Real.exp_pos _)).mpr
          linarith
    have h := LowTransport.rankOne_moment_bound m k C L hL t ht (by simpa using htC) v hv
    apply le_trans ?_ h
    dsimp only [θ]
    nlinarith [pow_pos hθ k]


end BstLean.Part56.LowMoment
