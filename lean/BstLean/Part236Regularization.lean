import BstLean.Part236Moments

namespace BstLean.Part236
open Real MeasureTheory
open BstLean.Part130 BstLean.Part134 BstLean.Part136

noncomputable def regularSp (e d y : ℝ) : ℝ := 1 / ((1 + e) * √(max y d))
noncomputable def regularP (e d y : ℝ) : ℝ := 1 / ((1 + e) * max y d)

lemma regularSp_pos {e d y : ℝ} (he : 0 < e) (hd : 0 < d) :
    0 < regularSp e d y := by
  unfold regularSp
  have hm : 0 < max y d := hd.trans_le (le_max_right _ _)
  positivity

lemma regularP_pos {e d y : ℝ} (he : 0 < e) (hd : 0 < d) :
    0 < regularP e d y := by
  unfold regularP
  have hm : 0 < max y d := hd.trans_le (le_max_right _ _)
  positivity

lemma regularSp_price {e d y : ℝ} :
    1 / regularSp e d y = (1 + e) * √(max y d) := by simp [regularSp]
lemma regularP_price {e d y : ℝ} :
    1 / regularP e d y = (1 + e) * max y d := by simp [regularP]

lemma regular_strict {e d y : ℝ} (he : 0 < e) (hd : 0 < d) (hy : 0 ≤ y) :
    y < (1 + e) ^ 2 * max y d ∧ y < (1 + e) * max y d := by
  have hm : 0 < max y d := hd.trans_le (le_max_right _ _)
  have hey := mul_pos he hm
  have he2 := mul_nonneg (sq_nonneg e) hm.le
  constructor <;> nlinarith [le_max_left y d]

theorem regular_goodHid {n : ℕ} (hn : 4096 ≤ n) {e d : ℝ}
    (he : 0 < e) (hd : 0 < d) (θ : HidParam (2 * n) (mW n)) :
    θ ∈ goodHid (2 * n) (mW n)
      ((regularSp e d (yK θ)) ^ 2) (regularP e d (yD θ)) := by
  have hB := markScale_pos hn
  have hK := (regular_strict he hd (yK_nonneg θ)).1
  have hD := (regular_strict he hd (yD_nonneg θ)).2
  have hmk : 0 < max (yK θ) d := hd.trans_le (le_max_right _ _)
  have hmd : 0 < max (yD θ) d := hd.trans_le (le_max_right _ _)
  have hs := Real.sq_sqrt hmk.le
  have hsp := regularSp_pos (y := yK θ) he hd
  have hp := regularP_pos (y := yD θ) he hd
  have hkEq : 1 / regularSp e d (yK θ) ^ 2 = (1 + e) ^ 2 * max (yK θ) d := by
    rw [← one_div_pow, regularSp_price, mul_pow, hs]
  have hdEq := regularP_price (e := e) (d := d) (y := yD θ)
  change errK θ < markScale n / regularSp e d (yK θ) ^ 2 ∧
    errD θ < markScale n / regularP e d (yD θ)
  constructor
  · rw [div_eq_mul_one_div, hkEq]
    have hh := mul_lt_mul_of_pos_left hK hB
    simpa [yK, mul_div_cancel₀, ne_of_gt hB] using hh
  · rw [div_eq_mul_one_div, hdEq]
    have hh := mul_lt_mul_of_pos_left hD hB
    simpa [yD, mul_div_cancel₀, ne_of_gt hB] using hh

lemma sqrt_max_le {y d : ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) :
    √(max y d) ≤ √y + √d := by
  rcases le_total y d with h | h
  · rw [max_eq_right h]; linarith [sqrt_nonneg y]
  · rw [max_eq_left h]; linarith [sqrt_nonneg d]

lemma max_le_add {y d : ℝ} (hy : 0 ≤ y) (hd : 0 ≤ d) : max y d ≤ y + d :=
  max_le (by linarith) (by linarith)
end BstLean.Part236
