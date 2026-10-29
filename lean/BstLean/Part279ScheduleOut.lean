import BstLean.Part189All
import BstLean.Part189WorldConstants

/-!
Part 279 (C1): the operation schedule of Part 189 with every `.reserve` leaf
replaced by a written-out list of charged operations.

Source of the formulas: `proofs/option-n/theorem7-01-statement-program.tex`
(`theorem7-01`), "Ordered program" (lines 90 to 205), "First-layer sphere moments"
(lines 209 to 296). Each list comment names the formula and the step.

Rules of the count (as in `theorem7-01`, lines 53 to 62): add, sub, mul, div, sqrt,
compare and relu cost one operation. `max(0, v)` is one `relu`. `max(a, v)` for a
constant `a` is `sub, relu, add`. Rational constants and loop bounds are free.
Negation is one `sub`.

What this file proves: the written-out schedule has no reserve, costs at most the
Part 189 schedule, and is below `1.0003 * 2 n^7`.
What this file does not prove: that the listed operations compute the program
`progOut (statedDesign n)`. The lists are matched to the program by inspection.
-/

namespace BstLean.Part189
/-- The names of the `.reserve` leaves of a schedule. -/
def Work.reserves : Work → List String
  | .empty => []
  | .op _ => []
  | .thenDo a b => a.reserves ++ b.reserves
  | .repeat _ a => a.reserves
  | .reserve name _ => [name]
end BstLean.Part189

namespace BstLean.Part279
open BstLean.Part130 BstLean.Part189
noncomputable section

lemma ops_reserves (os : List ChargedOp) : (ops os).reserves = [] := by
  induction os with
  | nil => rfl
  | cons o os ih => simp [ops, Work.reserves, ih]

lemma chain_reserves (ws : List Work) (h : ∀ w ∈ ws, w.reserves = []) :
    (chain ws).reserves = [] := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [chain, Work.reserves, h w (by simp), List.nil_append]
    exact ih (fun v hv => h v (by simp [hv]))

lemma dotWork_reserves (k : ℕ) : (dotWork k).reserves = [] := by
  simp [dotWork, Work.reserves]
lemma matVecWork_reserves (r k : ℕ) : (matVecWork r k).reserves = [] := by
  simp [matVecWork, Work.reserves, dotWork_reserves]
lemma binomialSetupConstant_reserves (J : ℕ) : (binomialSetupConstant J).reserves = [] := by
  simp [binomialSetupConstant, Work.reserves, ops_reserves]
lemma sharedMean_reserves (J : ℕ) : (sharedMean J).reserves = [] := by
  simp [sharedMean, Work.reserves, ops_reserves]
lemma twoMomentAtom_reserves : twoMomentAtom.reserves = [] := by
  simp [twoMomentAtom, ops_reserves]

lemma agentWork_reserves (n : ℕ) : (agentWork n).reserves = [] := by
  simp [agentWork, chain, Work.reserves, binomialSetupConstant_reserves, agentRhoWork,
    agentFirstRowWork, agentVarianceWork, matVecWork_reserves, dotWork_reserves,
    sharedMean_reserves, ops_reserves]

/-! ### R1: World constants (`theorem7-01`, step 1, lines 93 to 113) -/

/-- Step 1 constants.
* `(n-1)` multiplications by `2j/(2j+1)`: the product in `c̃_N` (line 101).
* `div, mul`: `π̃⁻¹` and the product times `π̃⁻¹` (line 100).
* two `repeat T_π [mul, div, add]`: `A_{T_π}(1/5)` and `A_{T_π}(1/239)`, three
  operations per term (lines 84, 87, 96).
* `mul, mul, sub`: `π̃ = 16A − 4A` (line 96).
* `mul, mul, sub`: `d̃_N = N⁻¹ − 2c̃_N²` (line 102); the first `mul` is `c̃_N²`.
* `mul, mul`: `r̃ = 2N c̃_N²` (line 103).
* `mul, sub, sqrt, div, add, mul, add, div`: `κ̃` outside `Q` (lines 110 to 112):
  `r̃²`, `1 − r̃²`, `√`, `π̃/2`, `+ Q`, `× r̃`, `+`, `÷ π̃`.
* `repeat T_κ [mul, mul, div, add]`: `Q_{T_κ}(r̃)`, four operations per term (line 86). -/
def worldConstantsWork (n : ℕ) : Work := chain [
  .repeat (n - 1) (.op .mul),
  ops [.div, .mul],
  .repeat (worldPiLength n) (ops [.mul, .div, .add]),
  .repeat (worldPiLength n) (ops [.mul, .div, .add]),
  ops [.mul, .mul, .sub],
  ops [.mul, .mul, .sub],
  ops [.mul, .mul],
  ops [.mul, .sub, .sqrt, .div, .add, .mul, .add, .div],
  .repeat (worldKappaLength n) (ops [.mul, .mul, .div, .add])]

theorem worldConstantsWork_cost (n : ℕ) :
    (worldConstantsWork n).cost =
      (n - 1) + 6 * worldPiLength n + 4 * worldKappaLength n + 18 := by
  simp [worldConstantsWork, chain, Work.cost, ops_cost] <;> omega

theorem worldConstantsWork_le {n : ℕ} (hn : 8000 ≤ n) :
    (worldConstantsWork n).cost ≤ 2 * n := by
  have h := worldConstantCount_le hn
  rw [worldConstantsWork_cost]
  unfold worldConstantCount at h
  omega

/-- The tail of `worldWork`, copied from Part 189 (the proof `worldWork_eq` is `rfl`). -/
def worldTail (n : ℕ) : Work :=
  let m := mW n
  let J := worldSigns n
  (.thenDo (.repeat m (.thenDo (dotWork (2 * n)) (ops [.sqrt, .mul])))
  (.thenDo (.thenDo (.repeat (m - 1) (.op .add)) (ops [.div, .mul, .sqrt]))
  (.thenDo (matVecWork m m)
  (.thenDo (binomialSetup J)
  (.thenDo (.repeat (J + 1) (.op .mul))
  (.thenDo (.repeat m (sharedMean J))
  (.thenDo (matVecWork n m)
  (.thenDo (dotWork m) (ops [.mul, .mul, .mul, .div, .sub, .mul, .relu, .mul, .sqrt])))))))))

theorem worldWork_eq (n : ℕ) :
    worldWork n = .thenDo (.reserve "World constants" (2 * n)) (worldTail n) := rfl

def worldWork' (n : ℕ) : Work := .thenDo (worldConstantsWork n) (worldTail n)

theorem worldWork'_le {n : ℕ} (hn : 8000 ≤ n) : (worldWork' n).cost ≤ (worldWork n).cost := by
  have h := worldConstantsWork_le hn
  rw [worldWork_eq]
  simp only [worldWork', Work.cost]
  omega

/-! ### R2, R2': row conversions and combinations (`theorem7-01`, lines 233 to 296) -/

/-- Even `n`, one row at one node (29 operations). Line numbers refer to `theorem7-01`.
* `mul`: `m = s_g α_i` (line 157).
* `mul`: `k = √(max(0,1−s_g²))·κ_i`; the root is per node, see `nodeWork'`.
* `sub, div`: `d = −m/k` (line 242).
* `compare ×3`: the branch tests `k = 0`, `m ≥ k`, `m ≤ −k` (lines 274 to 276).
* `mul`: `d²`. `mul`: `d³`.
* `mul ×3, sub ×3`: `J_j(d) = Σc_{r,j} − d^{j+1}·Horner_j(d²)` for `j = 0,1,2` (line 237);
  the three Horner lists are the loop `repeat n [mul, add, mul]` in `sphereRowWork'`.
* `mul, mul, add, mul`: `ā = N_P(m J₀ + k J₁)` (line 244).
* `mul ×7, add ×2, mul`: `ē = N_P(m²J₀ + 2mkJ₁ + k²J₂)`: `m²`, `m²J₀`, `mk`, `mkJ₁`,
  `2mkJ₁`, `k²`, `k²J₂`, two sums, `× N_P` (line 245). -/
def evenRowOps : List ChargedOp := [
  .mul, .mul,
  .sub, .div,
  .compare, .compare, .compare,
  .mul, .mul,
  .mul, .mul, .mul, .sub, .sub, .sub,
  .mul, .mul, .add, .mul,
  .mul, .mul, .mul, .mul, .mul, .mul, .mul, .add, .add, .mul]

/-- Odd `n`: the operations added to `evenRowOps` (19 operations).
* `compare`: the case `v ≤ 1/2` (line 289).
* `sub, div, sqrt, div, mul, sub`: `π_o/2 − 2Q(√((1−v)/2))` for `1/2 < v < 1`:
  `1−v`, `/2`, `√`, `π_o/2`, `2Q`, `−` (lines 290 to 291).
* `compare, sub`: the sign restore for negative arguments (line 291).
* `sub, sqrt`: `1 − d²` and one root for half-integer powers (lines 293 to 294).
* `mul, mul`: `J₁ = (1−d²)^{P+3/2}/(2P+3)` (line 266).
* `sub`: `J₂ = K_{P+1} − K_{P+2}` (line 267).
* `relu, mul, sub, relu, add`: `ā ← max(0,ā)`, `ā²`, and `ē ← max(ē, ā²) = ā² + relu(ē − ā²)`
  (lines 295 to 296). -/
def oddExtraOps : List ChargedOp := [
  .compare,
  .sub, .div, .sqrt, .div, .mul, .sub,
  .compare, .sub,
  .sub, .sqrt,
  .mul, .mul,
  .sub,
  .relu, .mul, .sub, .relu, .add]

/-- Row work. The loops are those of `sphereRowWork`. Odd `n` also has the inverse-sine
series loop (`Q_{T_o}`, 4 operations per term) and the `K_r` recurrence loop. -/
def sphereRowWork' (n : ℕ) : Work :=
  if n % 2 = 0 then
    .thenDo (.repeat n (ops [.mul, .add, .mul])) (ops evenRowOps)
  else
    .thenDo (.repeat (oddAsinLength n) (ops [.mul, .mul, .div, .add]))
      (.thenDo (.repeat n (ops [.mul, .mul, .sub, .mul, .mul, .sub, .add, .div]))
        (ops (evenRowOps ++ oddExtraOps)))

theorem evenRowOps_length : evenRowOps.length = 29 := rfl
theorem oddExtraOps_length : oddExtraOps.length = 19 := rfl

theorem sphereRowWork'_even {n : ℕ} (hn : n % 2 = 0) :
    (sphereRowWork' n).cost = 3 * n + 29 := by
  simp [sphereRowWork', hn, Work.cost, ops_cost, evenRowOps_length] <;> omega

theorem sphereRowWork'_odd {n : ℕ} (hn : n % 2 ≠ 0) :
    (sphereRowWork' n).cost = 4 * oddAsinLength n + 8 * n + 48 := by
  simp [sphereRowWork', hn, Work.cost, ops_cost, evenRowOps_length, oddExtraOps_length] <;> omega

theorem sphereRowWork'_le (n : ℕ) : (sphereRowWork' n).cost ≤ (sphereRowWork n).cost := by
  by_cases he : n % 2 = 0
  · rw [sphereRowWork'_even he, sphereRowWork_even he]; omega
  · rw [sphereRowWork'_odd he, sphereRowWork_odd he]; omega

theorem sphereRowWork'_reserves (n : ℕ) : (sphereRowWork' n).reserves = [] := by
  by_cases he : n % 2 = 0 <;>
    simp [sphereRowWork', he, Work.reserves, ops_reserves]

/-- One node. Same as `nodeWork` with the written-out row. -/
def nodeWork' (n : ℕ) : Work :=
  .thenDo (matVecWork (n ^ 2) (n ^ 2))
    (.repeat (n ^ 2) (.thenDo (sphereRowWork' n)
      (.repeat (conditionalSigns n + 1) twoMomentAtom)))
def gridWork' (n : ℕ) : Work := .repeat (gridNodes n) (nodeWork' n)

theorem nodeWork'_le (n : ℕ) : (nodeWork' n).cost ≤ (nodeWork n).cost := by
  have h := sphereRowWork'_le n
  simp only [nodeWork', nodeWork, Work.cost]
  gcongr

theorem gridWork'_le (n : ℕ) : (gridWork' n).cost ≤ (gridWork n).cost := by
  simp only [gridWork', gridWork, Work.cost]
  exact Nat.mul_le_mul_left _ (nodeWork'_le n)

theorem gridWork'_reserves (n : ℕ) : (gridWork' n).reserves = [] := by
  simp [gridWork', nodeWork', Work.reserves, matVecWork_reserves, sphereRowWork'_reserves,
    twoMomentAtom_reserves]

/-! ### R3 to R6: setup -/

/-- R3, per row: `α_i = a_i·u` (`= μ_i/|ĉ|` for `ĉ ≠ 0`, `div`) and
`κ_i = √max(0, q_i − α_i²)` (`mul, sub, relu, sqrt`), line 149 to 150. Five per row. -/
def rowDataWork (n : ℕ) : Work := .repeat (n ^ 2) (ops [.div, .mul, .sub, .relu, .sqrt])

/-- R3, once. `P ≤ n/2`, so each loop has `n/2 + 1` steps.
* `repeat [mul]`: `N_P⁻¹ = 2∏ 2r/(2r+1)` (line 235).
* `repeat [12 ops]`: the coefficients `(−1)^r C(P,r)/(2r+j+1)`, `j = 0,1,2` (line 237).
* `repeat [add ×3]`: the sums `Σ_r c_{r,j}`.
* `repeat [mul, div]`: `D_r = D_{r−1}(2r+2)/(2r+1)` (line 252).
* `repeat T_{π,o} [mul, div, add ×... ]`: `π_o` by two Machin sums, six per term (line 288).
* `mul, mul, sub, div`: `π_o = 16A − 4A` and `N_P = D_P/π_o` (line 252). -/
def commonConstWork (n : ℕ) : Work := chain [
  .repeat (n / 2 + 1) (.op .mul),
  .repeat (n / 2 + 1) (ops [.mul, .div, .div, .div, .div, .mul, .mul, .mul, .sub, .add, .mul, .div]),
  .repeat (n / 2 + 1) (ops [.add, .add, .add]),
  .repeat (n / 2 + 1) (ops [.mul, .div]),
  .repeat (oddPiLength n) (ops [.mul, .div, .add, .mul, .div, .add]),
  ops [.mul, .mul, .sub, .div]]

/-- R5, scalars free of the node: `s_c = |ĉ|/ρ` (`div`), `6τ₀/ρ` (`mul, div`), `L`, `H` (`sub, add`),
`H − L` and `Δ = (H−L)/J_s` (`sub, mul`), lines 146 and 153.
Per node: `s_g = L + (g+1/2)Δ` (`mul, add`), `s_g²`, `1−s_g²`, `max(0,·)`, `√` (`mul, sub, relu, sqrt`),
`L + gΔ` for the binary search boundary (`mul, add`), and the two grid tests (`compare ×2`). -/
def gridConstWork (n : ℕ) : Work :=
  .thenDo (ops [.div, .mul, .div, .sub, .add, .sub, .mul])
    (.repeat (gridNodes n)
      (ops [.mul, .add, .mul, .sub, .relu, .sqrt, .mul, .add, .compare, .compare]))

/-- R6: `e_b = |b|²/n` (`div`; `|b|²` is in `agentWork`), `√e_b` (`sqrt`), `γ_A = 2/n` (`div`),
`τ₀²` (`mul`), `|ĉ| = √(|ĉ|²)` (`sqrt`; `|ĉ|²` is in `agentRhoWork`), and the test `ĉ = 0`
(`compare`), lines 146 and 145. -/
def scalarWork : Work := ops [.div, .sqrt, .div, .mul, .sqrt, .compare]

def setupWork' (n : ℕ) : Work := chain [
  rowDataWork n, commonConstWork n, binomialSetupConstant (conditionalSigns n),
  gridConstWork n, scalarWork]

lemma le_mF {n : ℕ} (hn : 1 ≤ n) : n ≤ mF n := by
  have h1 : (n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h2 : (n : ℝ) ≤ (mF n : ℝ) := le_trans h1 (Nat.le_ceil _)
  exact_mod_cast h2

theorem setupWork'_le {n : ℕ} (hn : 8000 ≤ n) : (setupWork' n).cost ≤ (setupWork n).cost := by
  have hT := oddPiLength_le hn
  have hF := le_mF (by omega : 1 ≤ n)
  have h1 : n ≤ n ^ 2 := by nlinarith
  have h2 : n ^ 2 ≤ n ^ 3 := by nlinarith
  have hJ : conditionalSigns n + 1 = mF n := conditional_atoms (by omega)
  simp only [setupWork', setupWork, chain, rowDataWork, commonConstWork, gridConstWork,
    scalarWork, binomialSetupConstant_cost, Work.cost, ops_cost, gridNodes]
  simp only [List.length_cons, List.length_nil, chain_cost, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  unfold conditionalSigns at hJ ⊢
  omega

theorem setupWork'_reserves (n : ℕ) : (setupWork' n).reserves = [] := by
  simp [setupWork', chain, rowDataWork, commonConstWork, gridConstWork, scalarWork,
    Work.reserves, ops_reserves, binomialSetupConstant_reserves]

/-! ### R7, R8: one draw -/

/-- R7: `F(y) > t`: `F₁y`, `relu`, `F₂`, `relu`, `f₃`, and the comparison with `t`. -/
def classifierWork (n : ℕ) : Work := chain [
  matVecWork (mF n) n, .repeat (mF n) (.op .relu),
  matVecWork (mF n) (mF n), .repeat (mF n) (.op .relu),
  matVecWork 1 (mF n), .op .compare]

/-- R8, lines 181 to 196 of `theorem7-01`.
* `mul, add`: `a_x = |ĉ| + τ₀Z`.
* `dotWork (n−1)`: `Σ G_i²`. `mul`: `r_x² = τ₀² ΣG²`.
* `mul, add, sqrt, div`: `s = a_x/√(a_x² + r_x²)`.
* `compare ×2`: clip to `[L,H]`.
* `repeat (log₂ J_s + 1) compare`: binary search over the `J_s` cell boundaries.
* `div`: `λ̃ = f̃/√e_b`.
* `mul, sub, sub, relu, add, mul`: `S̃ = γ_A max(1/5, ω̃ − f̃²)`, where
  `max(1/5, x) = 1/5 + relu(x − 1/5)`.
* `sqrt`: `√S̃`.
* `repeat n [mul, mul, add]`: `y = λ̃ c_A + √S̃ η`. -/
def drawArithWork (n : ℕ) : Work := chain [
  ops [.mul, .add], dotWork (n - 1), .op .mul,
  ops [.mul, .add, .sqrt, .div], ops [.compare, .compare],
  .repeat (Nat.log 2 (gridNodes n) + 1) (.op .compare),
  .op .div, ops [.mul, .sub, .sub, .relu, .add, .mul], .op .sqrt,
  .repeat n (ops [.mul, .mul, .add])]

def drawWork' (n : ℕ) : Work := .thenDo (classifierWork n) (drawArithWork n)

theorem classifierWork_cost_le {n : ℕ} (hn : 1 ≤ n) :
    (classifierWork n).cost ≤ classifierAllowance n := by
  have hm := one_le_mF hn
  have h1 := matVecWork_cost_add_rows (r := mF n) hn
  have h2 := matVecWork_cost_add_rows (r := mF n) hm
  have h3 := matVecWork_cost_add_rows (r := 1) hm
  simp only [classifierWork, chain_cost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Work.cost]
  unfold classifierAllowance
  ring_nf at h1 h2 h3 ⊢
  omega

theorem log_gridNodes_lt (n : ℕ) : Nat.log 2 (gridNodes n) < n + 9 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [gridNodes]
  · rw [Nat.log_lt_iff_lt_pow (by norm_num) (by unfold gridNodes; omega)]
    have h1 : n < 2 ^ n := by
      first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow_self n | exact Nat.lt_pow_self (by norm_num)
    have h2 : 2 ^ (n + 9) = 512 * 2 ^ n := by rw [pow_add]; ring
    unfold gridNodes
    omega

theorem drawArithWork_cost_le {n : ℕ} (hn : 2 ≤ n) :
    (drawArithWork n).cost ≤ 10 * n + 100 := by
  have hd := dotWork_cost (n - 1)
  have hl := log_gridNodes_lt n
  simp only [drawArithWork, chain_cost, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Work.cost, ops_cost, List.length_cons, List.length_nil]
  omega

theorem drawWork'_le {n : ℕ} (hn : 2 ≤ n) : (drawWork' n).cost ≤ (drawWork n).cost := by
  have h1 := classifierWork_cost_le (by omega : 1 ≤ n)
  have h2 := drawArithWork_cost_le hn
  simp only [drawWork', drawWork, Work.cost]
  omega

theorem drawWork'_reserves (n : ℕ) : (drawWork' n).reserves = [] := by
  simp [drawWork', classifierWork, drawArithWork, chain, Work.reserves, ops_reserves,
    matVecWork_reserves, dotWork_reserves]

/-! ### The whole schedule -/

def orderedWork' (n : ℕ) : Work :=
  .thenDo (worldWork' n)
    (.thenDo (agentWork n)
      (.thenDo (setupWork' n)
        (.thenDo (gridWork' n)
          (.thenDo (.repeat draws (drawWork' n))
            (.thenDo (.repeat draws (.op .add)) outputWork)))))

theorem worldWork'_reserves (n : ℕ) : (worldWork' n).reserves = [] := by
  simp [worldWork', worldConstantsWork, worldTail, chain, Work.reserves, ops_reserves,
    dotWork_reserves, matVecWork_reserves, binomialSetup, sharedMean_reserves]

theorem noReserve_orderedWork' (n : ℕ) : (orderedWork' n).reserves = [] := by
  simp [orderedWork', Work.reserves, worldWork'_reserves, agentWork_reserves,
    setupWork'_reserves, gridWork'_reserves, drawWork'_reserves, outputWork, ops_reserves]

theorem orderedWork'_le {n : ℕ} (hn : 8000 ≤ n) :
    (orderedWork' n).cost ≤ (orderedWork n).cost := by
  have h1 := worldWork'_le hn
  have h2 := setupWork'_le hn
  have h3 := gridWork'_le n
  have h4 := Nat.mul_le_mul_left draws (drawWork'_le (by omega : 2 ≤ n))
  simp only [orderedWork', orderedWork, Work.cost]
  omega

theorem paperCount'_lt {n : ℕ} (hn : 8000 ≤ n) :
    ((orderedWork' n).cost : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : ((orderedWork' n).cost : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    exact_mod_cast orderedWork'_le hn
  have h2 := orderedWork_lt_8000 hn
  have h3 : (1.0003 : ℝ) = 10003 / 10000 := by norm_num
  rw [h3]
  exact lt_of_le_of_lt h h2

/-- info: 'BstLean.Part279.noReserve_orderedWork'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noReserve_orderedWork'
/-- info: 'BstLean.Part279.orderedWork'_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms orderedWork'_le
/-- info: 'BstLean.Part279.paperCount'_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paperCount'_lt

end
end BstLean.Part279
