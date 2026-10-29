import BstLean.Part195Rotation

/-! Factorial bounds for the coefficients in the BE row estimate. -/
namespace BstLean.Part202
open Real
open BstLean.Part162 (gmom gmom_nonneg)

/-- The BE scale is the exact rational number 26.9. -/
noncomputable def beta : ℝ := 269 / 10

lemma beta_pos : 0 < beta := by norm_num [beta]

lemma gmom_even_succ (p : ℕ) :
    gmom (2 * (p + 1)) = gmom (2 * p) * (2 * p + 1) := by
  rw [BstLean.Part162.gmom_even, BstLean.Part162.gmom_even, Finset.prod_range_succ]

/-- The square of an odd double factorial is at most the even factorial. -/
lemma gmom_sq_le_factorial (p : ℕ) :
    gmom (2 * p) ^ 2 ≤ ((2 * p).factorial : ℝ) := by
  induction p with
  | zero =>
    rw [BstLean.Part162.gmom_even]
    norm_num
  | succ p ih =>
    rw [gmom_even_succ, mul_pow]
    calc gmom (2 * p) ^ 2 * (2 * p + 1 : ℝ) ^ 2
        ≤ ((2 * p).factorial : ℝ) * ((2 * p + 2) * (2 * p + 1)) := by
          gcongr
          nlinarith [Nat.cast_nonneg (α := ℝ) p]
      _ = ((2 * (p + 1)).factorial : ℝ) := by
          rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega,
            Nat.factorial_succ, Nat.factorial_succ]
          push_cast
          ring

/-- A geometric analytic majorant starts at order four. -/
lemma pi_tail (k : ℕ) (hk : 4 ≤ k) :
    π ^ k * (k + 1 : ℝ) ≤ beta ^ (k - 2) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  push_cast
  induction j with
  | zero =>
    norm_num
    have hp : π ≤ 22 / 7 := Real.pi_lt_d4.le.trans (by norm_num)
    calc π ^ 4 * 5 ≤ (22 / 7 : ℝ) ^ 4 * 5 := by gcongr
      _ ≤ beta ^ 2 := by norm_num [beta]
  | succ j ih =>
    push_cast
    have hp : π ≤ 22 / 7 := Real.pi_lt_d4.le.trans (by norm_num)
    have hstep : π * (4 + j + 2 : ℝ) ≤ beta * (4 + j + 1 : ℝ) := by
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have := mul_le_mul_of_nonneg_right hp (by positivity : (0 : ℝ) ≤ 4 + j + 2)
      norm_num [beta] at *
      nlinarith
    have e : 4 + (j + 1) - 2 = (4 + j - 2) + 1 := by omega
    rw [e, pow_succ]
    calc π ^ (4 + (j + 1)) * (4 + (j + 1) + 1 : ℝ)
        = π ^ (4 + j) * (π * (4 + j + 2 : ℝ)) := by
          rw [show 4 + (j + 1) = (4 + j) + 1 by omega, pow_succ]
          push_cast
          ring
      _ ≤ π ^ (4 + j) * (beta * (4 + j + 1 : ℝ)) := by gcongr
      _ = (π ^ (4 + j) * (4 + j + 1 : ℝ)) * beta := by ring
      _ ≤ beta ^ (4 + j - 2) * beta :=
          mul_le_mul_of_nonneg_right ih beta_pos.le

/-- Even-order coefficient, with the exact Gaussian moment. -/
noncomputable def evenCoefficient (p : ℕ) : ℝ := π ^ (2 * p) * gmom (2 * p) ^ 2

/-- Odd-order coefficient from interpolation at the next even order. -/
noncomputable def oddCoefficient (p : ℕ) : ℝ :=
  π ^ (2 * p + 1) * gmom (2 * (p + 1)) ^ (2 * (2 * p + 1 : ℝ) / (2 * p + 2))

lemma evenCoefficient_le (p : ℕ) (hp : 2 ≤ p) :
    evenCoefficient p ≤ ((2 * p).factorial : ℝ) * beta ^ (2 * p - 2) := by
  have htail := pi_tail (2 * p) (by omega)
  push_cast at htail
  have hpi : π ^ (2 * p) ≤ beta ^ (2 * p - 2) := by
    calc π ^ (2 * p) ≤ π ^ (2 * p) * (2 * p + 1 : ℝ) := by
          nlinarith [pow_nonneg Real.pi_pos.le (2 * p), Nat.cast_nonneg (α := ℝ) p]
      _ ≤ _ := htail
  unfold evenCoefficient
  calc π ^ (2 * p) * gmom (2 * p) ^ 2
      ≤ beta ^ (2 * p - 2) * ((2 * p).factorial : ℝ) :=
        mul_le_mul hpi (gmom_sq_le_factorial p) (sq_nonneg _)
          (pow_nonneg beta_pos.le _)
    _ = _ := by ring

lemma oddCoefficient_three : oddCoefficient 1 ≤ (3).factorial * beta ^ (3 - 2) := by
  have hg : gmom 4 = 3 := by
    rw [show 4 = 2 * 2 by omega, BstLean.Part162.gmom_even]
    norm_num [Finset.prod_range_succ]
  have he : oddCoefficient 1 ^ 2 = π ^ 6 * 27 := by
    norm_num [oddCoefficient, hg, mul_pow]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
    ring
  have hp : π ≤ 3.1416 := Real.pi_lt_d4.le
  have hb : oddCoefficient 1 ^ 2 ≤ (6 * beta) ^ 2 := by
    rw [he]
    calc π ^ 6 * 27 ≤ (3.1416 : ℝ) ^ 6 * 27 := by gcongr
      _ ≤ (6 * beta) ^ 2 := by norm_num [beta]
  norm_num
  exact le_of_sq_le_sq hb (by norm_num [beta])

/-- The odd coefficient also satisfies the crude factorial bound. -/
lemma oddCoefficient_crude (p : ℕ) :
    oddCoefficient p ≤ π ^ (2 * p + 1) * (((2 * p + 2).factorial : ℝ)) := by
  have hp0 : (0 : ℝ) ≤ (2 * p + 1 : ℝ) / (2 * p + 2) := by positivity
  have hp1 : (2 * p + 1 : ℝ) / (2 * p + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have he : gmom (2 * (p + 1)) ^ (2 * (2 * p + 1 : ℝ) / (2 * p + 2)) =
      (gmom (2 * (p + 1)) ^ 2) ^ ((2 * p + 1 : ℝ) / (2 * p + 2)) := by
    rw [← Real.rpow_natCast_mul (gmom_nonneg _) 2]
    congr 1
    ring
  unfold oddCoefficient
  rw [he]
  gcongr
  calc (gmom (2 * (p + 1)) ^ 2) ^ ((2 * p + 1 : ℝ) / (2 * p + 2))
      ≤ (((2 * p + 2).factorial : ℝ)) ^ ((2 * p + 1 : ℝ) / (2 * p + 2)) := by
        apply Real.rpow_le_rpow (sq_nonneg _) _ hp0
        simpa [show 2 * (p + 1) = 2 * p + 2 by omega] using gmom_sq_le_factorial (p + 1)
    _ ≤ _ := Real.rpow_le_self_of_one_le
      (by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos _)) hp1

lemma oddCoefficient_le (p : ℕ) (hp : 1 ≤ p) :
    oddCoefficient p ≤ ((2 * p + 1).factorial : ℝ) * beta ^ (2 * p + 1 - 2) := by
  by_cases he : p = 1
  · subst p
    exact oddCoefficient_three
  · have htail := pi_tail (2 * p + 1) (by omega)
    push_cast at htail
    calc oddCoefficient p ≤ π ^ (2 * p + 1) * (((2 * p + 2).factorial : ℝ)) :=
          oddCoefficient_crude p
      _ = (π ^ (2 * p + 1) * (2 * p + 1 + 1 : ℝ)) * ((2 * p + 1).factorial : ℝ) := by
          rw [show 2 * p + 2 = (2 * p + 1) + 1 by omega, Nat.factorial_succ]
          push_cast
          ring
      _ ≤ beta ^ (2 * p + 1 - 2) * ((2 * p + 1).factorial : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
          simpa only [show 2 * p + 1 - 2 = 2 * p - 1 by omega] using htail
      _ = _ := by ring

/-- The coefficient uses parity to select the paper's two formulas. -/
noncomputable def coefficient (k : ℕ) : ℝ :=
  if Even k then evenCoefficient (k / 2) else oddCoefficient (k / 2)

/-- Every BE coefficient has the stated factorial majorant, with no upper order cap. -/
theorem coefficient_factorial (k : ℕ) (hk : 3 ≤ k) :
    coefficient k ≤ (k.factorial : ℝ) * beta ^ (k - 2) := by
  unfold coefficient
  split_ifs with he
  · have hmod : k % 2 = 0 := Nat.even_iff.mp he
    have heq : 2 * (k / 2) = k := by omega
    simpa only [heq] using evenCoefficient_le (k / 2) (by omega)
  · have hmod : k % 2 = 1 := by
      have := Nat.mod_lt k (by omega : 0 < 2)
      have hn := mt Nat.even_iff.mpr he
      omega
    have heq : 2 * (k / 2) + 1 = k := by omega
    simpa only [heq] using oddCoefficient_le (k / 2) (by omega)

/-- In particular, the complete finite range requested by the paper is checked. -/
theorem coefficient_finite (k : ℕ) (hk : 3 ≤ k) (_h200 : k ≤ 200) :
    coefficient k ≤ (k.factorial : ℝ) * beta ^ (k - 2) :=
  coefficient_factorial k hk

/-- The analytic order tail includes every order above the finite range. -/
theorem coefficient_tail (k : ℕ) (hk : 201 ≤ k) :
    coefficient k ≤ (k.factorial : ℝ) * beta ^ (k - 2) :=
  coefficient_factorial k (by omega)

end BstLean.Part202
