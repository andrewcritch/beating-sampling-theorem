import BstLean.Part189Series
import BstLean.Part189Widths

/-!
Part 189: operation schedules and upper budgets.

`Work` records charged operations and loops. It has no register arguments or evaluator.
`reserve` records an upper budget for a subroutine. It is not a primitive operation.
The count theorems concern this schedule. They do not prove its value.
The sphere reserve covers the row conversions, recurrences and moment combinations.
-/

namespace BstLean.Part189
open BstLean.Part130
noncomputable section

inductive ChargedOp
  | add | sub | mul | div | sqrt | relu | compare
  deriving DecidableEq

inductive Work
  | empty
  | op (o : ChargedOp)
  | thenDo (a b : Work)
  | repeat (k : ℕ) (a : Work)
  | reserve (name : String) (upper : ℕ)

def Work.cost : Work → ℕ
  | .empty => 0
  | .op _ => 1
  | .thenDo a b => a.cost + b.cost
  | .repeat k a => k * a.cost
  | .reserve _ upper => upper

def ops : List ChargedOp → Work
  | [] => .empty
  | o :: os => .thenDo (.op o) (ops os)

theorem ops_cost (os : List ChargedOp) : (ops os).cost = os.length := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [ops, Work.cost, ih, Nat.add_comm]

def dotWork (k : ℕ) : Work :=
  .thenDo (.repeat k (.op .mul)) (.repeat (k - 1) (.op .add))
def matVecWork (rows cols : ℕ) : Work := .repeat rows (dotWork cols)

theorem dotWork_cost (k : ℕ) : (dotWork k).cost = k + (k - 1) := by
  simp [dotWork, Work.cost]
theorem matVecWork_cost (rows cols : ℕ) :
    (matVecWork rows cols).cost = rows * (cols + (cols - 1)) := by
  simp [matVecWork, Work.cost, dotWork_cost]

/-- Count the stated halvings, the two-operation weight recurrence, and the atoms. -/
def binomialSetup (J : ℕ) : Work :=
  .thenDo (.repeat J (.op .div))
    (.thenDo (.repeat J (ops [.mul, .div]))
      (.thenDo (ops [.sqrt, .div]) (.repeat (J + 1) (.op .mul))))

theorem binomialSetup_cost (J : ℕ) : (binomialSetup J).cost = 4 * J + 3 := by
  simp [binomialSetup, Work.cost, ops_cost]
  omega

/-- This variant uses the free rational constant `p₀ = 2⁻ᴶ`. -/
def binomialSetupConstant (J : ℕ) : Work :=
  .thenDo (.repeat J (ops [.mul, .div]))
    (.thenDo (ops [.sqrt, .div]) (.repeat (J + 1) (.op .mul)))

theorem binomialSetupConstant_cost (J : ℕ) : (binomialSetupConstant J).cost = 3 * J + 3 := by
  simp [binomialSetupConstant, Work.cost, ops_cost]
  omega

/-- Form an affine value, its ReLU, two weighted moments, and two accumulations. -/
def twoMomentAtom : Work := ops [.mul, .add, .relu, .mul, .mul, .add, .add]
theorem twoMomentAtom_cost : twoMomentAtom.cost = 7 := by rfl

/-- The noise offset is shared across rows; the sum starts with its first term. -/
def sharedMean (J : ℕ) : Work :=
  .thenDo (.repeat (J + 1) (ops [.add, .relu, .mul])) (.repeat J (.op .add))
theorem sharedMean_cost (J : ℕ) : (sharedMean J).cost = 4 * J + 3 := by
  simp [sharedMean, Work.cost, ops_cost]
  omega

/-- Step 2, with the `2n` upper budget for the constants of step 1. -/
def worldWork (n : ℕ) : Work :=
  let m := mW n
  let J := worldSigns n
  .thenDo (.reserve "World constants" (2 * n))
  (.thenDo (.repeat m (.thenDo (dotWork (2 * n)) (ops [.sqrt, .mul])))
  (.thenDo (.thenDo (.repeat (m - 1) (.op .add)) (ops [.div, .mul, .sqrt]))
  (.thenDo (matVecWork m m)
  (.thenDo (binomialSetup J)
  (.thenDo (.repeat (J + 1) (.op .mul))
  (.thenDo (.repeat m (sharedMean J))
  (.thenDo (matVecWork n m)
  (.thenDo (dotWork m) (ops [.mul, .mul, .mul, .div, .sub, .mul, .relu, .mul, .sqrt])))))))))

lemma worldWork_cost {n : ℕ} (hn : 1 ≤ n) :
    (worldWork n).cost + n =
      2 * mW n ^ 2 + mW n * (6 * n + 4 * worldSigns n + 6) + 2 * n + 5 * worldSigns n + 14 := by
  have hm := one_le_mW hn
  obtain ⟨a, ha⟩ : ∃ a, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, mW n = b + 1 := ⟨mW n - 1, by omega⟩
  unfold worldWork
  simp only [Work.cost, dotWork_cost, matVecWork_cost, binomialSetup_cost, sharedMean_cost, ops_cost]
  rw [hb, ha]
  have he : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
  simp only [Nat.add_sub_cancel, he]
  norm_num only [List.length_cons, List.length_nil, mul_one]
  ring

lemma worldSigns_ge {n : ℕ} (hn : 1 ≤ n) : n ≤ worldSigns n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (1 : ℝ) ≤ Real.sqrt n := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hx)
  have hp : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hx (by norm_num)
  have hbase : (n : ℝ) ^ 3 * Real.sqrt n ≤ (mW n : ℝ) := by
    unfold mW
    have he := half_power n 3
    norm_num at he
    rw [he]
    exact Nat.le_ceil _
  have hsq : (n : ℝ) ^ 2 ≤ (mW n : ℝ) := by
    calc (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := hp
      _ ≤ (n : ℝ) ^ 3 * Real.sqrt n := le_mul_of_one_le_right (by positivity) hs
      _ ≤ _ := hbase
  have hr : (n : ℝ) ≤ Real.sqrt (mW n : ℝ) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hsq
  have hc := Nat.le_ceil (Real.sqrt (mW n : ℝ))
  unfold worldSigns
  exact_mod_cast le_trans hr hc

theorem worldWork_le {n : ℕ} (hn : 1 ≤ n) : (worldWork n).cost ≤ worldAllowance n := by
  have h := worldWork_cost hn
  have hj := worldSigns_ge hn
  unfold worldAllowance
  omega

/-- The even row allowance evaluates three Horner lists. The odd row allowance
uses four operations per inverse-sine term and eight operations per dimension
for the powers and `K` recurrence. The fixed reserve has 100 operations. -/
def sphereRowWork (n : ℕ) : Work :=
  if n % 2 = 0 then
    .thenDo (.repeat n (ops [.mul, .add, .mul])) (.reserve "row conversions and combinations" 100)
  else
    .thenDo (.repeat (oddAsinLength n) (ops [.mul, .mul, .div, .add]))
      (.thenDo (.repeat n (ops [.mul, .mul, .sub, .mul, .mul, .sub, .add, .div]))
        (.reserve "row conversions and combinations" 100))

theorem sphereRowWork_even {n : ℕ} (hn : n % 2 = 0) : (sphereRowWork n).cost = 3 * n + 100 := by
  simp [sphereRowWork, hn, Work.cost, ops_cost]
  omega
theorem sphereRowWork_odd {n : ℕ} (hn : n % 2 ≠ 0) :
    (sphereRowWork n).cost = 4 * oddAsinLength n + 8 * n + 100 := by
  simp [sphereRowWork, hn, Work.cost, ops_cost]
  omega
theorem sphereRowWork_le {n : ℕ} (hn : 8000 ≤ n) : (sphereRowWork n).cost ≤ 30 * n + 100 := by
  by_cases he : n % 2 = 0
  · rw [sphereRowWork_even he]; omega
  · rw [sphereRowWork_odd he]
    have h := oddAsinLength_le hn
    omega

def nodeWork (n : ℕ) : Work :=
  .thenDo (matVecWork (n ^ 2) (n ^ 2))
    (.repeat (n ^ 2) (.thenDo (sphereRowWork n)
      (.repeat (conditionalSigns n + 1) twoMomentAtom)))
def gridWork (n : ℕ) : Work := .repeat (gridNodes n) (nodeWork n)

theorem nodeWork_cost (n : ℕ) : (nodeWork n).cost =
    n ^ 2 * (n ^ 2 + (n ^ 2 - 1)) +
      n ^ 2 * ((sphereRowWork n).cost + 7 * (conditionalSigns n + 1)) := by
  simp only [nodeWork, Work.cost, matVecWork_cost, twoMomentAtom_cost]
  ring

theorem nodeWork_le {n : ℕ} (hn : 8000 ≤ n) : (nodeWork n).cost ≤ nodeAllowance n := by
  rw [nodeWork_cost]
  have hrow := sphereRowWork_le hn
  have hdot : n ^ 2 + (n ^ 2 - 1) ≤ 2 * n ^ 2 := by omega
  calc
    _ ≤ n ^ 2 * (2 * n ^ 2) + n ^ 2 * (30 * n + 100 + 7 * (conditionalSigns n + 1)) := by
      exact add_le_add (Nat.mul_le_mul_left _ hdot)
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right hrow _))
    _ = nodeAllowance n := by unfold nodeAllowance; ring

theorem gridWork_le {n : ℕ} (hn : 8000 ≤ n) : (gridWork n).cost ≤ conditionalAllowance n := by
  exact Nat.mul_le_mul_left (gridNodes n) (nodeWork_le hn)

def chain : List Work → Work
  | [] => .empty
  | w :: ws => .thenDo w (chain ws)

theorem chain_cost (ws : List Work) : (chain ws).cost = (ws.map Work.cost).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [chain, Work.cost, ih]

def agentFirstRowWork (n : ℕ) : Work := chain [
  dotWork n, dotWork n, ops [.sqrt, .mul, .div],
  .repeat (n + 1) (ops [.add, .relu, .mul, .mul]),
  .repeat n (ops [.add, .add]), ops [.mul, .mul, .mul]]

def agentVarianceWork (m : ℕ) : Work := chain [
  .repeat (m - 1) (.op .add), dotWork m, ops [.sub, .mul, .sqrt]]

def agentRhoWork (n : ℕ) : Work := .thenDo (dotWork n) (ops [.mul, .mul, .add, .sqrt])

/-- This schedule uses the free rational p₀. It divides the common second-layer
weights by ρ before the row sums. Thus it forms b directly, and stores no b′. -/
def agentWork (n : ℕ) : Work := chain [
  binomialSetupConstant n, agentRhoWork n,
  .repeat (n ^ 2) (agentFirstRowWork n), agentVarianceWork (n ^ 2),
  matVecWork (n ^ 2) (n ^ 2), .repeat (n + 1) (.op .mul),
  .repeat (n + 1) (.op .div), .repeat (n ^ 2) (sharedMean n),
  matVecWork n (n ^ 2), dotWork (n ^ 2), .repeat 4 (.op .compare)]

lemma dotWork_cost_add_one {k : ℕ} (hk : 1 ≤ k) : (dotWork k).cost + 1 = 2 * k := by
  rw [dotWork_cost]
  omega

lemma matVecWork_cost_add_rows {r k : ℕ} (hk : 1 ≤ k) :
    (matVecWork r k).cost + r = 2 * r * k := by
  rw [matVecWork_cost]
  calc r * (k + (k - 1)) + r = r * (k + (k - 1) + 1) := by ring
    _ = 2 * r * k := by rw [show k + (k - 1) + 1 = 2 * k by omega]; ring

lemma agentFirstRowWork_cost {n : ℕ} (hn : 1 ≤ n) : (agentFirstRowWork n).cost = 10 * n + 8 := by
  have h := dotWork_cost_add_one hn
  simp only [agentFirstRowWork, chain_cost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Work.cost, ops_cost, List.length_cons, List.length_nil]
  omega

lemma agentVarianceWork_cost {m : ℕ} (hm : 1 ≤ m) : (agentVarianceWork m).cost = 3 * m + 1 := by
  have h := dotWork_cost_add_one hm
  simp only [agentVarianceWork, chain_cost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Work.cost, ops_cost, List.length_cons, List.length_nil]
  omega

lemma agentRhoWork_cost {n : ℕ} (hn : 1 ≤ n) : (agentRhoWork n).cost = 2 * n + 3 := by
  have h := dotWork_cost_add_one hn
  simp only [agentRhoWork, Work.cost, ops_cost, List.length_cons, List.length_nil]
  omega

def setupWork (n : ℕ) : Work :=
  .thenDo (.reserve "row data and common odd constant" (100 * n ^ 3))
    (.thenDo (.reserve "conditional binomial lists" (100 * conditionalSigns n))
      (.thenDo (.reserve "grid construction" (100 * gridNodes n)) (.reserve "scalar setup" 100)))
def drawWork (n : ℕ) : Work :=
  .thenDo (.reserve "classifier evaluation and comparison" (classifierAllowance n))
    (.reserve "latitude, clipping, binary search and conversions" (10 * n + 100))
def outputWork : Work := ops [.div, .mul, .compare, .compare]

theorem agentWork_cost {n : ℕ} (hn : 1 ≤ n) : (agentWork n).cost + 9 = agentAllowance n := by
  have hm : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have hM := matVecWork_cost_add_rows (r := n ^ 2) hm
  have hO := matVecWork_cost_add_rows (r := n) hm
  have hN := dotWork_cost_add_one hm
  simp only [agentWork, chain_cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Work.cost, binomialSetupConstant_cost, agentRhoWork_cost hn, agentFirstRowWork_cost hn,
    agentVarianceWork_cost hm, sharedMean_cost]
  unfold agentAllowance
  ring_nf at hM hO hN ⊢
  omega

theorem agentWork_le {n : ℕ} (hn : 1 ≤ n) : (agentWork n).cost ≤ agentAllowance n := by
  have h := agentWork_cost hn
  omega

theorem setupWork_cost (n : ℕ) : (setupWork n).cost = setupAllowance n := by
  simp [setupWork, Work.cost, setupAllowance]
  omega
theorem drawWork_cost (n : ℕ) : (drawWork n).cost = drawAllowance n := by
  simp [drawWork, Work.cost, drawAllowance]
  omega
theorem outputWork_cost : outputWork.cost = 4 := rfl

/-- The ordered budget contains both primitive loops and named reserves. -/
def orderedWork (n : ℕ) : Work :=
  .thenDo (worldWork n)
    (.thenDo (agentWork n)
      (.thenDo (setupWork n)
        (.thenDo (gridWork n)
          (.thenDo (.repeat draws (drawWork n))
            (.thenDo (.repeat draws (.op .add)) outputWork)))))

theorem orderedWork_cost (n : ℕ) : (orderedWork n).cost =
    (worldWork n).cost + (agentWork n).cost + setupAllowance n + (gridWork n).cost +
      draws * drawAllowance n + draws + 4 := by
  simp [orderedWork, Work.cost, setupWork_cost, drawWork_cost, outputWork_cost]
  omega

theorem orderedWork_le {n : ℕ} (hn : 8000 ≤ n) : (orderedWork n).cost ≤ paperCount n := by
  rw [orderedWork_cost]
  have hw := worldWork_le (by omega : 1 ≤ n)
  have hg := gridWork_le hn
  have ha := agentWork_le (by omega : 1 ≤ n)
  unfold paperCount
  omega

end
end BstLean.Part189
