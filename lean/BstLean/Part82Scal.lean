import Mathlib

/-!
# Part 82: scalar inequalities for the transfer to the coefficient sphere
-/

namespace BstLean.Part82

/-- The conditional mean bounds of the two lower pieces, in units of the floor, on `‖u‖² ≤ 2n`. -/
lemma scal_bounds {N r vH vu t Wfu CF X2 X3 v3 : ℝ} (hN : 1000000 ≤ N) (hr0 : 0 ≤ r)
    (hr : r ≤ 2 * N) (hvu : 0 ≤ vu) (ht : 0 ≤ t) (hvH0 : 0 ≤ vH) (hvH : vH ≤ 2 * vu + 18 * t * r)
    (hW : 555 / 100 * vu + 277 / 10 * t ≤ Wfu) (hCF0 : 0 ≤ CF) (hCF : CF ≤ 4)
    (hX20 : 0 ≤ X2) (hX30 : 0 ≤ X3) (hv30 : 0 ≤ v3)
    (hX2 : X2 ≤ 4 * vH * r) (hX3 : X3 ≤ 18 * t * r ^ 2 + 50 * N * t) (hv3 : v3 ≤ 9 * t * r) :
    (4 * X2 + 19 * vH) + 5 * (4 * X3 + 19 * v3 + 163 * t) ≤ 95 * N ^ 2 * Wfu ∧
    (101 / 100 * CF * X2 + (6 * CF + 907 / 100) * vH) / N +
      5 * ((101 / 100 * CF * X3 + (6 * CF + 907 / 100) * v3 + 55 * CF * t) / N) ≤ 95 * N * Wfu ∧
    N * vH ≤ 13 / 10 * N ^ 2 * Wfu ∧ N * t * r ≤ 73 / 1000 * N ^ 2 * Wfu := by
  have hN0 : 0 < N := by linarith
  have hNN : 1000000 * N ≤ N ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hN hN0.le
  have hN2 : (1000000 : ℝ) ^ 2 ≤ N ^ 2 := by nlinarith
  have a_tr : t * r ≤ 2 * (N * t) := by
    have := mul_le_mul_of_nonneg_left hr ht; linarith
  have hr2 : r ^ 2 ≤ 4 * N ^ 2 := by
    have := mul_le_mul hr hr hr0 (by linarith); rw [sq, sq]; linarith
  have a_tr2 : t * r ^ 2 ≤ 4 * (N ^ 2 * t) := by
    have := mul_le_mul_of_nonneg_left hr2 ht; linarith
  have a_Nt : 1000000 * (N * t) ≤ N ^ 2 * t := by
    have := mul_le_mul_of_nonneg_right hNN ht; linarith
  have a_t : (1000000 : ℝ) ^ 2 * t ≤ N ^ 2 * t := mul_le_mul_of_nonneg_right hN2 ht
  have a_vu : (1000000 : ℝ) ^ 2 * vu ≤ N ^ 2 * vu := mul_le_mul_of_nonneg_right hN2 hvu
  have a_Nvu : 1000000 * (N * vu) ≤ N ^ 2 * vu := by
    have := mul_le_mul_of_nonneg_right hNN hvu; linarith
  have b_vH : vH ≤ 2 * vu + 36 * (N * t) := by linarith
  have b_NvH : N * vH ≤ 2 * (N * vu) + 36 * (N ^ 2 * t) := by
    have := mul_le_mul_of_nonneg_left b_vH hN0.le
    have e : N * (2 * vu + 36 * (N * t)) = 2 * (N * vu) + 36 * (N ^ 2 * t) := by ring
    linarith
  have b_vHr : vH * r ≤ 4 * (N * vu) + 72 * (N ^ 2 * t) := by
    have := mul_le_mul_of_nonneg_left hr hvH0
    linarith
  have hWN : N ^ 2 * (555 / 100 * vu + 277 / 10 * t) ≤ N ^ 2 * Wfu :=
    mul_le_mul_of_nonneg_left hW (sq_nonneg N)
  have hNt0 : 0 ≤ N * t := mul_nonneg hN0.le ht
  have hNvu0 : 0 ≤ N * vu := mul_nonneg hN0.le hvu
  have hQ0 : 0 ≤ N ^ 2 * t := mul_nonneg (sq_nonneg N) ht
  have hP0 : 0 ≤ N ^ 2 * vu := mul_nonneg (sq_nonneg N) hvu
  have c_X2 : X2 ≤ 16 * (N * vu) + 288 * (N ^ 2 * t) := by linarith
  have c_X3 : X3 ≤ 72 * (N ^ 2 * t) + 50 * (N * t) := by linarith
  have c_v3 : v3 ≤ 18 * (N * t) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith
  · have e : (101 / 100 * CF * X2 + (6 * CF + 907 / 100) * vH) / N +
        5 * ((101 / 100 * CF * X3 + (6 * CF + 907 / 100) * v3 + 55 * CF * t) / N) =
        ((101 / 100 * CF * X2 + (6 * CF + 907 / 100) * vH) +
          5 * (101 / 100 * CF * X3 + (6 * CF + 907 / 100) * v3 + 55 * CF * t)) / N := by ring
    rw [e, div_le_iff₀ hN0]
    have d1 : CF * X2 ≤ 4 * X2 := mul_le_mul_of_nonneg_right hCF hX20
    have d2 : CF * vH ≤ 4 * vH := mul_le_mul_of_nonneg_right hCF hvH0
    have d3 : CF * X3 ≤ 4 * X3 := mul_le_mul_of_nonneg_right hCF hX30
    have d4 : CF * v3 ≤ 4 * v3 := mul_le_mul_of_nonneg_right hCF hv30
    have d5 : CF * t ≤ 4 * t := mul_le_mul_of_nonneg_right hCF ht
    have e2 : 95 * N * Wfu * N = 95 * (N ^ 2 * Wfu) := by ring
    rw [e2]
    linarith
  · linarith
  · have : N * t * r = N * (t * r) := by ring
    rw [this]
    have h1 := mul_le_mul_of_nonneg_left a_tr hN0.le
    have e : N * (2 * (N * t)) = 2 * (N ^ 2 * t) := by ring
    linarith

end BstLean.Part82
