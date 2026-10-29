import BstLean.Part189Num
import BstLean.Part130Cost

namespace BstLean.Part189
open BstLean.Part130
noncomputable section

/-- One ordinary dense sample, including normalization and the final comparison. -/
def exactSampleCount (n : ℕ) : ℕ :=
  mlpCost (2 * n) (mW n) n + 3 * n + mlpCost n (n ^ 2) n + mlpCost n (mF n) 1 + 1

lemma mlpCost_formula {k m q : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    mlpCost k m q + q = 2 * m * k + 2 * m ^ 2 + 2 * q * m := by
  unfold mlpCost
  have hk' : 2 * k - 1 + 1 = 2 * k := by omega
  have hm' : 2 * m - 1 + 1 = 2 * m := by omega
  have he : m * (2 * k - 1) + m = 2 * m * k := by
    calc _ = m * ((2 * k - 1) + 1) := by ring
      _ = _ := by rw [hk']; ring
  have he' : m * (2 * m - 1) + m = 2 * m ^ 2 := by
    calc _ = m * ((2 * m - 1) + 1) := by ring
      _ = _ := by rw [hm']; ring
  have he'' : q * (2 * m - 1) + q = 2 * q * m := by
    calc _ = q * ((2 * m - 1) + 1) := by ring
      _ = _ := by rw [hm']; ring
  omega

theorem exactSampleCount_eq {n : ℕ} (hn : 1 ≤ n) :
    exactSampleCount n =
      2 * mW n ^ 2 + 6 * n * mW n + 2 * n ^ 4 + 4 * n ^ 3 +
      2 * n * mF n + 2 * mF n ^ 2 + 2 * mF n + n := by
  have hW := mlpCost_formula (k := 2 * n) (q := n) (by omega) (one_le_mW hn)
  have hA := mlpCost_formula (k := n) (m := n ^ 2) (q := n) hn (Nat.one_le_pow _ _ hn)
  have hF := mlpCost_formula (k := n) (q := 1) hn (one_le_mF hn)
  unfold exactSampleCount
  have hsum := congrArg₂ (fun a b : ℕ => a + b) hW (congrArg₂ (fun a b : ℕ => a + b) hA hF)
  ring_nf at hsum ⊢
  omega

theorem exactSampleCount_ge {n : ℕ} (hn : 1 ≤ n) : 2 * n ^ 7 ≤ exactSampleCount n := by
  have hw : n ^ 7 ≤ mW n ^ 2 := (mW_le_iff n (mW n)).mp le_rfl
  rw [exactSampleCount_eq hn]
  omega

/-- This compares arithmetic counts. It does not assert a probability lower bound. -/
theorem comparison_1139 {n : ℕ} (hn : 8000 ≤ n) :
    (113865 : ℝ) * paperCount n < (100 * 1139 : ℝ) * exactSampleCount n := by
  have hp := paperCount_lt_8000 hn
  have hs : 2 * (n : ℝ) ^ 7 ≤ (exactSampleCount n : ℝ) := by
    exact_mod_cast exactSampleCount_ge (by omega : 1 ≤ n)
  have hx : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx7 : 0 < (n : ℝ) ^ 7 := pow_pos hx 7
  nlinarith

end
end BstLean.Part189
