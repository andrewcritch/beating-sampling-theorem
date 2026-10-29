import BstLean.Part130Extra

/-!
Part 189: the upper allowances of the paper's finite arithmetic program.
These definitions are counts. They do not define an evaluator.
The tight conditional allowance applies at every dimension in this file.
-/

namespace BstLean.Part189
open BstLean.Part130
noncomputable section

def worldSigns (n : ℕ) : ℕ := ⌈Real.sqrt (mW n : ℝ)⌉₊
def globalSigns (n : ℕ) : ℕ := n
def conditionalSigns (n : ℕ) : ℕ := mF n - 1
def gridNodes (n : ℕ) : ℕ := 512 * n
def draws : ℕ := 10 ^ 12

def worldAllowance (n : ℕ) : ℕ :=
  2 * mW n ^ 2 + mW n * (6 * n + 4 * worldSigns n + 6) +
    6 * worldSigns n + 20
def agentAllowance (n : ℕ) : ℕ :=
  2 * n ^ 4 + 16 * n ^ 3 + 15 * n ^ 2 + 6 * n + 21
def classifierAllowance (n : ℕ) : ℕ :=
  2 * n * mF n + 2 * mF n ^ 2 + 2 * mF n + 1
def nodeAllowance (n : ℕ) : ℕ :=
  2 * n ^ 4 + 7 * n ^ 2 * (conditionalSigns n + 1) + 30 * n ^ 3 + 100 * n ^ 2
def conditionalAllowance (n : ℕ) : ℕ := gridNodes n * nodeAllowance n
def setupAllowance (n : ℕ) : ℕ :=
  100 * n ^ 3 + 100 * conditionalSigns n + 100 * gridNodes n + 100
def drawAllowance (n : ℕ) : ℕ := classifierAllowance n + 10 * n + 100
def paperCount (n : ℕ) : ℕ :=
  worldAllowance n + agentAllowance n + conditionalAllowance n + setupAllowance n +
    draws * drawAllowance n + draws + 10

theorem conditional_atoms {n : ℕ} (hn : 1 ≤ n) : conditionalSigns n + 1 = mF n := by
  have := one_le_mF hn
  simp only [conditionalSigns]
  omega

theorem paperCount_eq {n : ℕ} (hn : 1 ≤ n) :
    paperCount n =
      2 * mW n ^ 2 + mW n * (6 * n + 4 * worldSigns n + 6) + 6 * worldSigns n + 20 +
      (2 * n ^ 4 + 16 * n ^ 3 + 15 * n ^ 2 + 6 * n + 21) +
      512 * n * (2 * n ^ 4 + 7 * n ^ 2 * mF n + 30 * n ^ 3 + 100 * n ^ 2) +
      (100 * n ^ 3 + 100 * (mF n - 1) + 51200 * n + 100) +
      10 ^ 12 * (2 * n * mF n + 2 * mF n ^ 2 + 2 * mF n + 1 + 10 * n + 100) +
      10 ^ 12 + 10 := by
  unfold paperCount worldAllowance agentAllowance conditionalAllowance nodeAllowance
    setupAllowance drawAllowance classifierAllowance
  rw [conditional_atoms hn]
  simp only [gridNodes, conditionalSigns, draws]
  ring

end
end BstLean.Part189
