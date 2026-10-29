import BstLean.Part88Arith
import BstLean.Part86Tail

/-!
# Part 89, auxiliary arithmetic: the Christoffel constant at `D = 2k`, and the size of `DWr`
-/

namespace BstLean.Part89

open BstLean.Part88 (Sodd SS SE Sodd_mono Sodd_nonneg Sodd_le)
open BstLean.Part86 (DWr JR DWr_eq choose2_86 choose_mono86)
open BstLean.Part36 (DD DD_eq)

/-- The Christoffel constant of the even/odd transfer at degree `2k`, off-centre `1/(4k)`. -/
theorem SE_two_k_le (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 1000) :
    SE (2 * k) β (1 / (4 * (k : ℝ))) ≤ 61 / 100 * (k : ℝ) + 111 / 100 := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have e1 : 2 * k / 2 = k := Nat.mul_div_cancel_left k (by norm_num)
  have e2 : (2 * k - 1) / 2 = k - 1 := by omega
  have hSk := Sodd_le k
  -- the penalty term
  have hx : (5 : ℝ) / 4 * (1 / (4 * (k : ℝ))) ^ 2 = 5 / (64 * (k : ℝ) ^ 2) := by
    field_simp; ring
  have hx0 : (0 : ℝ) ≤ 5 / (64 * (k : ℝ) ^ 2) := by positivity
  have hpen : 5 / (64 * (k : ℝ) ^ 2) * Sodd k ≤ 5 / 384 * ((k : ℝ) + 13) := by
    have a := mul_le_mul_of_nonneg_left hSk hx0
    refine a.trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hk0.le (sub_nonneg.mpr hk2), sq_nonneg (k : ℝ),
      mul_nonneg (mul_nonneg hk0.le hk0.le) (sub_nonneg.mpr hk2)]
  have hpen' : 5 / (64 * (k : ℝ) ^ 2) * Sodd (k - 1) ≤ 5 / 384 * ((k : ℝ) + 13) :=
    (mul_le_mul_of_nonneg_left (Sodd_mono (Nat.sub_le k 1)) hx0).trans hpen
  have hpen0 : 0 ≤ 5 / (64 * (k : ℝ) ^ 2) * Sodd (k - 1) :=
    mul_nonneg hx0 (Sodd_nonneg _)
  have c1 : (((k / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 2 := by
    have b := Nat.cast_div_le (α := ℝ) (m := k) (n := 2)
    push_cast at b; linarith
  have c2 : ((((k - 1) / 2 : ℕ) : ℝ)) ≤ (k : ℝ) / 2 := by
    have b := Nat.cast_div_le (α := ℝ) (m := k - 1) (n := 2)
    have c : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    push_cast at b; linarith
  have c20 : (0 : ℝ) ≤ (((k - 1) / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold SE
  rw [e1, e2]
  apply max_le
  · unfold SS
    rw [hx]; linarith
  · unfold SS
    rw [hx]
    set A : ℝ := (((k - 1) / 2 : ℕ) : ℝ) + 1 + 5 / (64 * (k : ℝ) ^ 2) * Sodd (k - 1) with hA
    have hA0 : 0 ≤ A := by rw [hA]; linarith
    have hA1 : A ≤ (k : ℝ) / 2 + 1 + 5 / 384 * ((k : ℝ) + 13) := by rw [hA]; linarith
    have h3 : 1 + 3 * β ≤ 1003 / 1000 := by linarith
    calc (1 + 3 * β) * A ≤ 1003 / 1000 * A := mul_le_mul_of_nonneg_right h3 hA0
      _ ≤ 1003 / 1000 * ((k : ℝ) / 2 + 1 + 5 / 384 * ((k : ℝ) + 13)) :=
          mul_le_mul_of_nonneg_left hA1 (by norm_num)
      _ ≤ 61 / 100 * (k : ℝ) + 111 / 100 := by linarith

theorem DD_pos (n d : ℕ) (hn : 1 ≤ n) : 0 < DD n d := by
  rw [DD_eq]
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 < (n + d).choose d := Nat.choose_pos (by omega)
  exact mul_pos hn' (by exact_mod_cast hc)

theorem DWr_ge_cube (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 100 ≤ n) :
    (n : ℝ) ^ 3 / 3 ≤ DWr n (JR n d) := by
  rw [DWr_eq n d (by omega), DD_eq]
  have hc := choose_mono86 n d 2 hd
  have h2 := choose2_86 n
  have hc' : ((n + 2).choose 2 : ℝ) ≤ ((n + d).choose d : ℝ) := by exact_mod_cast hc
  have h2' : 2 * ((n + 2).choose 2 : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) := by exact_mod_cast h2
  have hn0 : (100 : ℝ) ≤ n := by exact_mod_cast hn
  have hd' : (d : ℝ) ≤ n := by exact_mod_cast hdn
  have a := mul_le_mul_of_nonneg_left hc' (by linarith : (0 : ℝ) ≤ n)
  have b := mul_le_mul_of_nonneg_left hd' (by linarith : (0 : ℝ) ≤ n)
  nlinarith [pow_pos (by linarith : (0 : ℝ) < n) 3, sq_nonneg (n : ℝ)]

theorem DWr_pos (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (hn : 100 ≤ n) :
    0 < DWr n (JR n d) := by
  have h := DWr_ge_cube n d hd hdn hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have : 0 < (n : ℝ) ^ 3 / 3 := by positivity
  linarith

end BstLean.Part89

#print axioms BstLean.Part89.SE_two_k_le
#print axioms BstLean.Part89.DD_pos
#print axioms BstLean.Part89.DWr_ge_cube
#print axioms BstLean.Part89.DWr_pos
