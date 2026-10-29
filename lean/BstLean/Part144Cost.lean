import BstLean.Part141Prog

/-!
# Part 144, items 3 and 4 (operation counts): one direct exact sample and the one-pass program

Role: `delegations/statements/p144-spec.md`, item 3 (`directSampleCost144`) and the operation
counts of item 4 (`compare144`). All counts are natural numbers of operations of the model
`RProg` of Part 130 (`+ − × ÷ √ max(0, ·)`, one each).

* `mlpCost_ge`, `mlpCost_le`: `2m² ≤ mlpCost k m q ≤ 2mk + 2m² + 2qm + 2m`.
* **`directSampleCost144`**: the direct program `sampleRProg` for one exact sample (`W(u)`, the
  normalization, `A`, `F`) uses at least `2·m_W²` operations plus one evaluation of `A` and one
  of `F`. This is the count of THIS program; it is not a lower bound for every program.
* **`progCost144`**: for `13225 ≤ n ≤ 16384` the arithmetic one-pass program of Part 141 with
  `k = 100n` cheap points uses at most `2.000005·m_W²` operations; `progCost144_coarse`: at most
  `2.002·m_W²`.
* **`progVsSample144`**: the program costs at most `1.001` direct exact samples.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

open BstLean.Part130 BstLean.Part141

/-- `2m² ≤ mlpCost k m q`: the middle matrix alone. -/
theorem mlpCost_ge (k m q : ℕ) : 2 * m ^ 2 ≤ mlpCost k m q := by
  have h : m * (2 * m - 1) + m = 2 * m ^ 2 := by
    cases m with
    | zero => rfl
    | succ j =>
      have e : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [e]; ring
  unfold mlpCost
  omega

/-- `mlpCost k m q ≤ 2mk + 2m² + 2qm + 2m`. -/
theorem mlpCost_le (k m q : ℕ) :
    mlpCost k m q ≤ 2 * (m * k) + 2 * m ^ 2 + 2 * (q * m) + 2 * m := by
  have h1 : m * (2 * k - 1) ≤ m * (2 * k) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h2 : m * (2 * m - 1) ≤ m * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 : q * (2 * m - 1) ≤ q * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have e1 : m * (2 * k) = 2 * (m * k) := by ring
  have e2 : m * (2 * m) = 2 * m ^ 2 := by ring
  have e3 : q * (2 * m) = 2 * (q * m) := by ring
  unfold mlpCost
  omega

/-- **`directSampleCost144`**: the direct program for one exact sample (`sampleRProg` of Part 130:
`W(u)`, the normalization, `A`, `F`) uses at least `2·m_W²` operations plus one evaluation of
`A` and one of `F`. This is the count of THIS program, not a lower bound for every program. -/
theorem directSampleCost144 (r n mW mA mF : ℕ) :
    2 * mW ^ 2 + mlpCost n mA n + mlpCost n mF 1 ≤ (sampleRProg r n mW mA mF).cost := by
  have h := mlpCost_ge (r * n) mW n
  simp only [sampleRProg, sampleRProgX, RProg.cost_mapOut, RProg.cost_mlpStep,
    RProg.rescaleStep, RProg.cost_bind, RProg.cost_inlProg]
  omega

/-- For `n ≥ 13225`: `5n + 2 + cost(A) + cost(F) ≤ 5n⁴`. -/
lemma evalCost_le {n : ℕ} (hn : 13225 ≤ n) :
    5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1 ≤ 5 * n ^ 4 := by
  have hA := mlpCost_le n (mA n) n
  have hF := mlpCost_le n (mF n) 1
  have hmF : mF n ≤ n ^ 2 := by
    rw [mF_le_iff]
    have e : (n ^ 2) ^ 2 = n ^ 3 * n := by ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have a1 : mA n * n = n ^ 3 := by unfold mA; ring
  have a2 : mA n ^ 2 = n ^ 4 := by unfold mA; ring
  have a3 : n * mA n = n ^ 3 := by unfold mA; ring
  have a4 : mA n = n ^ 2 := rfl
  have f1 : mF n * n ≤ n ^ 3 := by
    have := Nat.mul_le_mul_right n hmF
    have e : n ^ 2 * n = n ^ 3 := by ring
    omega
  have f2 : mF n ^ 2 ≤ n ^ 4 := by
    have := Nat.pow_le_pow_left hmF 2
    have e : (n ^ 2) ^ 2 = n ^ 4 := by ring
    omega
  have p2 : 13225 * n ≤ n ^ 2 := by
    have := Nat.mul_le_mul_right n hn
    have e : n * n = n ^ 2 := by ring
    omega
  have p3 : 13225 * n ^ 2 ≤ n ^ 3 := by
    have := Nat.mul_le_mul_right (n ^ 2) hn
    have e : n * n ^ 2 = n ^ 3 := by ring
    omega
  have p4 : 13225 * n ^ 3 ≤ n ^ 4 := by
    have := Nat.mul_le_mul_right (n ^ 3) hn
    have e : n * n ^ 3 = n ^ 4 := by ring
    omega
  omega

/-- **The arithmetic one-pass program with `k = 100n` cheap points uses at most
`2.000005·m_W²` operations**, for `13225 ≤ n ≤ 16384`. -/
theorem progCost144 {n : ℕ} (hn : 13225 ≤ n) (h16 : n ≤ 16384) :
    1000000 * (arithProg141 (100 * n) n).cost ≤ 2000005 * mW n ^ 2 := by
  have h := arithCost141_ratio (100 * n) (n := n) (by omega) h16
  have hS := evalCost_le hn
  have hm : n ^ 7 ≤ mW n ^ 2 := (mW_le_iff n (mW n)).mp le_rfl
  have hT : 100 * n * (5 * n + 2 + mlpCost n (mA n) n + mlpCost n (mF n) 1) ≤ 500 * n ^ 5 := by
    have := Nat.mul_le_mul_left (100 * n) hS
    have e : 100 * n * (5 * n ^ 4) = 500 * n ^ 5 := by ring
    omega
  have h2 : 13225 * 13225 ≤ n ^ 2 := by
    have := Nat.mul_le_mul hn hn
    have e : n * n = n ^ 2 := by ring
    omega
  have h7 : 174900625 * n ^ 5 ≤ n ^ 7 := by
    have := Nat.mul_le_mul_right (n ^ 5) h2
    have e : n ^ 2 * n ^ 5 = n ^ 7 := by ring
    omega
  omega

/-- The same count in a coarse form: at most `2.002·m_W²` operations. -/
theorem progCost144_coarse {n : ℕ} (hn : 13225 ≤ n) (h16 : n ≤ 16384) :
    1000 * (arithProg141 (100 * n) n).cost ≤ 2002 * mW n ^ 2 := by
  have h := progCost144 hn h16
  omega

/-- **The program costs at most `1.001` direct exact samples** (`13225 ≤ n ≤ 16384`,
`k = 100n` cheap points). -/
theorem progVsSample144 {n : ℕ} (hn : 13225 ≤ n) (h16 : n ≤ 16384) :
    1000 * (arithProg141 (100 * n) n).cost ≤
      1001 * (sampleRProg 2 n (mW n) (mA n) (mF n)).cost := by
  have h := progCost144_coarse hn h16
  have hs := directSampleCost144 2 n (mW n) (mA n) (mF n)
  omega

end BstLean.Part144

open BstLean.Part144 in
#print axioms mlpCost_ge
open BstLean.Part144 in
#print axioms mlpCost_le
open BstLean.Part144 in
#print axioms directSampleCost144
open BstLean.Part144 in
#print axioms progCost144
open BstLean.Part144 in
#print axioms progCost144_coarse
open BstLean.Part144 in
#print axioms progVsSample144
