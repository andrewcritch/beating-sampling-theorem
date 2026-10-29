import BstLean.Part271R3Bounds

/-! Dimension factors in the angular moment formulas of Part 218. -/
namespace BstLean.Part271.R3
open Real BstLean.Part130 BstLean.Part137 BstLean.Part218

noncomputable def angularMomentCore (N k : ℕ) : ℝ :=
  (N : ℝ)^k * angularMoment N k

noncomputable def offsetCore (N : ℕ) : ℝ := (N : ℝ)^2 * angularOffset N

noncomputable def aCore : ℝ := 1/(4*π)
noncomputable def bCore : ℝ := (1/2-3/(2*π))/2

noncomputable def j2Core (N : ℕ) : ℝ :=
  (offsetCore N + aCore)^2 + aCore^2 * (angularMomentCore N 2 - 1) +
    2*aCore*bCore*angularMomentCore N 3 / (N : ℝ) +
      bCore^2*angularMomentCore N 4 / (N : ℝ)^2

noncomputable def j4Core (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 5, ∑ l ∈ Finset.range (5-i),
    (Nat.choose 4 i : ℝ) * (Nat.choose (4-i) l : ℝ) * aCore^i *
      |offsetCore N|^(4-i-l) * bCore^l * angularMomentCore N (i+2*l) /
        (N : ℝ)^l

theorem rhoD_scale {N : ℕ} (hN : 0 < (N : ℝ)) (k : ℕ) :
    BstLean.Part36.rhoD N k = (N : ℝ)^k *
      ∏ j ∈ Finset.range k, (1+2*(j : ℝ)/(N : ℝ)) := by
  induction k with
  | zero => simp [BstLean.Part36.rhoD]
  | succ k ih =>
    simp only [BstLean.Part36.rhoD, Finset.prod_range_succ] at ih ⊢
    rw [ih, pow_succ]
    field_simp [ne_of_gt hN]
    <;> ring

theorem angularMomentCore_formula {N : ℕ} (hN : 0 < (N : ℝ)) (k : ℕ) :
    angularMomentCore N k = BstLean.Part29.gaussMom (2*k) /
      (∏ j ∈ Finset.range k, (1+2*(j : ℝ)/(N : ℝ))) := by
  unfold angularMomentCore angularMoment
  rw [rhoD_scale hN]
  field_simp [ne_of_gt hN]
  <;> ring

theorem angularMoment_one {N : ℕ} (hN : 0 < (N : ℝ)) :
    angularMoment N 1 = 1/(N : ℝ) := by
  norm_num [angularMoment, BstLean.Part29.gaussMom, BstLean.Part36.rhoD,
    Finset.prod_range_succ, Nat.doubleFactorial]

theorem angularJ2_scale {N : ℕ} (hN : 0 < (N : ℝ)) :
    angularJ2 N (angularOffset N) = j2Core N / (N : ℝ)^4 := by
  unfold angularJ2 j2Core angularMomentCore offsetCore angularA angularB aCore bCore
  rw [angularMoment_one hN]
  field_simp [ne_of_gt hN, Real.pi_ne_zero]
  <;> ring

theorem angularJ4_scale {N : ℕ} (hN : 0 < (N : ℝ)) :
    angularJ4 N (angularOffset N) = j4Core N / (N : ℝ)^8 := by
  unfold angularJ4 j4Core angularMomentCore offsetCore angularA angularB aCore bCore
  simp only [abs_mul, abs_pow, abs_of_nonneg (le_of_lt hN)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceMul, Nat.choose, Nat.cast_ofNat, pow_zero, mul_one,
    one_mul, add_zero, zero_add]
  field_simp [ne_of_gt hN, Real.pi_ne_zero]
  <;> ring

theorem cN_firstRatio {N : ℕ} (hN : 0 < (N : ℝ)) :
    cN N^2 = firstRatio N / (2*(N : ℝ)) := by
  unfold firstRatio
  field_simp [ne_of_gt hN]

theorem angularMoment_unscale {N : ℕ} (hN : 0 < (N : ℝ)) (k : ℕ) :
    angularMoment N k = angularMomentCore N k / (N : ℝ)^k := by
  unfold angularMomentCore
  field_simp [ne_of_gt hN]

theorem sqrt_div_square {x c : ℝ} (hc : 0 ≤ c) :
    √(x/c^2) = √x/c := by
  rw [Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc]

noncomputable def ba1Core (N : ℕ) : ℝ := (2/π)/(1+2/(N : ℝ))
noncomputable def ba2Core (N : ℕ) : ℝ := (5/4-2/π)/(1+2/(N : ℝ))

noncomputable def jbCore (N : ℕ) : ℝ :=
  ba1Core N^2 + ba2Core N^2 * angularMomentCore N 2 / (N : ℝ) +
    (1/(N : ℝ))/(4*(1+2/(N : ℝ))^2) +
    2*ba1Core N*ba2Core N*√(angularMomentCore N 2/(N : ℝ)) +
    ba1Core N*√(1/(N : ℝ))/(1+2/(N : ℝ)) +
    ba2Core N*(1/(N : ℝ))/(1+2/(N : ℝ))

theorem bA0_formula {N : ℕ} (hN : 0 < (N : ℝ)) :
    bA0 N = 1/(2*(N : ℝ)^2*((N : ℝ)+2)) := by
  have he : 1/(4*(N : ℝ)*((N : ℝ)+2))-1/(4*(N : ℝ)^2) =
      -(1/(2*(N : ℝ)^2*((N : ℝ)+2))) := by
    field_simp [ne_of_gt hN]
    <;> ring
  unfold bA0
  rw [he, abs_neg, abs_of_nonneg (by positivity)]

theorem angularJb_scale {N : ℕ} (hN : 0 < (N : ℝ)) :
    angularJb N = jbCore N/(N : ℝ)^5 := by
  have hs : √(angularMoment N 1*angularMoment N 2) =
      √(angularMomentCore N 2/(N : ℝ))/(N : ℝ) := by
    rw [angularMoment_one hN, angularMoment_unscale hN 2]
    rw [show (1/(N : ℝ))*(angularMomentCore N 2/(N : ℝ)^2) =
      (angularMomentCore N 2/(N : ℝ))/(N : ℝ)^2 by ring]
    exact sqrt_div_square hN.le
  unfold angularJb
  rw [hs, angularMoment_one hN, angularMoment_unscale hN 2, bA0_formula hN]
  unfold jbCore ba1Core ba2Core bA1 bA2
  field_simp [ne_of_gt hN, Real.pi_ne_zero]
  <;> ring

theorem offsetCore_bounds {N A : ℕ} (hA : 2 ≤ A) (hAN : A ≤ N) :
    BstLean.Part228.Bounds (offsetCore N)
      (-(A : ℝ)/(2*π*((A : ℝ)-1))) 0 := by
  have hN : 2 ≤ N := hA.trans hAN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : (2 : ℝ) ≤ A := by exact_mod_cast hA
  have han : (A : ℝ) ≤ N := by exact_mod_cast hAN
  have hnp : 0 < (N : ℝ) := by linarith
  have hap : 0 < (A : ℝ)-1 := by linarith
  have hnm : 0 < (N : ℝ)-1 := by linarith
  obtain ⟨hl, hu⟩ := angular_offset_bounds hN (le_refl N)
  have hlo := mul_le_mul_of_nonneg_left hl (sq_nonneg (N : ℝ))
  have hid : (N : ℝ)^2 * (-1/(2*π*(N : ℝ)*((N : ℝ)-1))) =
      -(N : ℝ)/(2*π*((N : ℝ)-1)) := by
    field_simp [ne_of_gt hnp]
    <;> ring
  rw [hid] at hlo
  refine ⟨le_trans ?_ hlo, mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hu⟩
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg pi_pos.le (sub_nonneg.mpr han)]

end BstLean.Part271.R3
