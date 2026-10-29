import BstLean.Part223OriginalEnergy
import BstLean.Part220Charge

/-! The four fields read one original second-layer matrix at every node. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part220

variable {n : ℕ}

noncomputable def originalFourErrors (c : Ret n) (i : Fin 4) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  ![originalLocationFluct c g M, originalLocationBias c g M,
    originalEnergyFluct c g M, originalEnergyBias c g M] i

noncomputable def originalFourNodePrice (c : Ret n) (g : ℕ) (O : ℝ)
    (d : RAData) (i : Fin 4) : ℝ :=
  ![2 * (sqrt (n : ℝ) *
      sqrt (tA n * ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2))) / 2) ^ 24 *
        (2 ^ 12 * ((12 : ℕ).factorial : ℝ)),
    d.locationBound n O,
    (BstLean.Part202.rowScale (stdGauss (Fin (n - 1))) (scaledLatitude c g)
      (sqrt (tA n * ((1 - nodeS c g ^ 2) * O ^ 2 / ((n : ℝ) - 2)))) *
        energyCoefficient18 n) ^ 18,
    d.energyBound n O] i

theorem originalFour_decomposition (c : Ret n) (g : ℕ)
    (M : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    originalFourErrors c 0 g M + originalFourErrors c 1 g M = exFn (withA2 c M) g ∧
    originalFourErrors c 2 g M + originalFourErrors c 3 g M = exWn (withA2 c M) g := by
  constructor <;> dsimp [originalFourErrors, originalLocationFluct, originalEnergyFluct] <;> ring

lemma measurable_originalFourErrors (c : Ret n) (i : Fin 4) (g : ℕ) :
    Measurable (originalFourErrors c i g) := by
  fin_cases i
  · exact measurable_originalLocationFluct c g
  · exact measurable_originalLocationBias c g
  · exact measurable_originalEnergyFluct c g
  · exact measurable_originalEnergyBias c g

theorem originalFour_node_supply (hn : 3 ≤ n) (c : Ret n) (g : ℕ)
    (hs : nodeS c g ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    (d : RAData) (h : NodeRASupply c g O d) (i : Fin 4) :
    ∫⁻ M, ENNReal.ofReal (|originalFourErrors c i g M| ^ biasOrder i)
      ∂gaussMat (mA n) (mA n) (tA n) ≤
      ENNReal.ofReal (originalFourNodePrice c g O d i) := by
  have hRA := originalBias_RA16_supply (by omega) c g hs hO hOp d h
  fin_cases i
  · exact originalLocationFluct_order24 hn c g hs hO hOp (sub_nonneg.mpr hs) le_rfl
  · exact hRA.1
  · exact originalEnergyFluct_order18 hn c g hs hO hOp
  · exact hRA.2

/-- Only deterministic scalar prices remain as inputs to the four Markov charges. -/
theorem originalFour_weighted_markov {J : ℕ} (hn : 3 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) [SFinite ν] (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O)
    (hOp : OpB (A1 c) O) (d : Fin J → RAData)
    (h : ∀ g, NodeRASupply c (node g) O (d g)) (B A : Fin 4 → ℝ)
    (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hp : ∀ i, ∫⁻ g, ENNReal.ofReal (originalFourNodePrice c (node g) O (d g) i) ∂ν ≤
      ENNReal.ofReal (B i ^ biasOrder i)) :
    (gaussMat (mA n) (mA n) (tA n)).real
      (⋃ i, momentBad ν (fun g => originalFourErrors c i (node g)) (biasOrder i) (A i)) ≤
      (B 0 / A 0) ^ 24 + (B 1 / A 1) ^ 16 +
        (B 2 / A 2) ^ 18 + (B 3 / A 3) ^ 16 := by
  refine four_bias_markov ν (gaussMat (mA n) (mA n) (tA n))
    (fun i g => originalFourErrors c i (node g)) B A ?_ hB hA ?_
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i (node g)
  · intro i
    exact (lintegral_mono fun g =>
      originalFour_node_supply hn c (node g) (hs g) hO hOp (d g) (h g) i).trans (hp i)

/-- The actual first-layer statistics and exact row moments supply all four fields. -/
theorem paperFour_weighted_markov {J : ℕ} (hn : 10 ≤ n)
    (wr : WRet n) (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) [SFinite ν]
    (node : Fin J → ℕ) (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (X : Matrix (Fin (mA n)) (Fin n) ℝ) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB X O)
    (Sm SM : Fin J → ℝ) (hSm : ∀ g, 0 < Sm g)
    (hmin : ∀ g, Sm g ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)))
    (hmax : ∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤ SM g)
    (hgap : ∀ g, 0 < Sm g / 2 -
      planeTraceCap n (nodeS (mkR wr (0, 0)) (node g)) O)
    (hk : ∀ g, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (X *ᵥ BstLean.Part161.xLat (mkR wr (0, 0))
        (nodeS (mkR wr (0, 0)) (node g)) (BstLean.Part53.unitF53 v)) j ≠ 0)
    (B A : Fin 4 → ℝ) (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hp : ∀ i, ∫⁻ g, ENNReal.ofReal (originalFourNodePrice (mkR wr (X, 0)) (node g) O
      (exactPaperRAData wr (node g) X O (Sm g) (SM g)) i) ∂ν ≤
        ENNReal.ofReal (B i ^ biasOrder i)) :
    (gaussMat (mA n) (mA n) (tA n)).real
      (⋃ i, momentBad ν (fun g => originalFourErrors (mkR wr (X, 0)) i (node g))
        (biasOrder i) (A i)) ≤
      (B 0 / A 0) ^ 24 + (B 1 / A 1) ^ 16 +
        (B 2 / A 2) ^ 18 + (B 3 / A 3) ^ 16 := by
  apply originalFour_weighted_markov (by omega) (mkR wr (X, 0)) ν node hs hO hOp
    (fun g => exactPaperRAData wr (node g) X O (Sm g) (SM g)) _ B A hB hA hp
  intro g
  exact exactPaperNodeRASupply hn wr hc (node g) (hs g) X hO hOp (hSm g)
    (hmin g) (hmax g) (hgap g) (hk g)

#print axioms originalFour_node_supply
#print axioms originalFour_decomposition
#print axioms originalFour_weighted_markov
#print axioms paperFour_weighted_markov
end BstLean.Part223
