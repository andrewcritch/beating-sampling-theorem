import BstLean.Part223CompleteSupply
import BstLean.Part223ScalarEvent

/-! Four supplied original-network moments give one conditional event charge. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part220

theorem four_bias_markov_prices {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (error : Fin 4 → G → Y → ℝ) (P A : Fin 4 → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i)))
    (hP : ∀ i, 0 ≤ P i) (hA : ∀ i, 0 < A i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error i g y| ^ biasOrder i) ∂σ ∂ν ≤
      ENNReal.ofReal (P i)) :
    σ.real (⋃ i, momentBad ν (error i) (biasOrder i) (A i)) ≤
      P 0 / A 0 ^ 24 + P 1 / A 1 ^ 16 + P 2 / A 2 ^ 18 + P 3 / A 3 ^ 16 := by
  let B := fun i => P i ^ ((biasOrder i : ℝ)⁻¹)
  have hB : ∀ i, 0 ≤ B i := fun i => rpow_nonneg (hP i) _
  have hp : ∀ i, B i ^ biasOrder i = P i := fun i =>
    Real.rpow_inv_natCast_pow (hP i) (biasOrder_pos i).ne'
  have h := four_bias_markov ν σ error B A hm hB hA (fun i => by rw [hp]; exact hM i)
  have he (i : Fin 4) : (B i / A i) ^ biasOrder i = P i / A i ^ biasOrder i := by
    rw [div_pow, hp]
  have h0 : (B 0 / A 0) ^ 24 = P 0 / A 0 ^ 24 := he 0
  have h1 : (B 1 / A 1) ^ 16 = P 1 / A 1 ^ 16 := he 1
  have h2 : (B 2 / A 2) ^ 18 = P 2 / A 2 ^ 18 := he 2
  have h3 : (B 3 / A 3) ^ 16 = P 3 / A 3 ^ 16 := he 3
  simpa only [h0, h1, h2, h3] using h

noncomputable def completeMomentPrices (n : ℕ) (Q O Sm SM C σ H : ℝ) : Fin 4 → ℝ :=
  let D := completeRAData (envelopeData n Q O Sm SM C C C) n O
  ![(BstLean.Part216.k24 * (sqrt (n : ℝ) *
        sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) / 2) * sqrt H) ^ 24,
    D.locationBound n O,
    (sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) * σ * energyCoefficient18 n) ^ 18 * H ^ 12 * Q ^ 6,
    D.energyBound n O]

lemma completeMomentPrices_nonneg (n : ℕ) (Q O Sm SM C σ H : ℝ) (i : Fin 4) :
    0 ≤ completeMomentPrices n Q O Sm SM C σ H i := by
  fin_cases i <;> dsimp [completeMomentPrices, RAData.locationBound, RAData.energyBound] <;>
    positivity

theorem paperOriginalFour_markov {n J : ℕ} (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (X : Matrix (Fin (mA n)) (Fin n) ℝ) {Q O Sm SM C σ H : ℝ}
    (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 < Sm) (hSM : 0 ≤ SM) (hC : 0 ≤ C)
    (hσ : 0 ≤ σ) (hH : 0 ≤ H)
    (hOp : OpB X O) (hE : X ∈ paperStatisticsEvent wr ν node C)
    (hcap : ∀ g, 1 - nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ Q)
    (hmin : ∀ g, Sm ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)))
    (hmax : ∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤ SM)
    (htrace : ∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤
      σ ^ 2 * (1 - nodeS (mkR wr (0, 0)) (node g) ^ 2))
    (hgap : 0 < envelopeGap n Q O Sm)
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12))
    (hk : ∀ g, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (X *ᵥ BstLean.Part161.xLat (mkR wr (0, 0))
        (nodeS (mkR wr (0, 0)) (node g)) (BstLean.Part53.unitF53 v)) j ≠ 0)
    (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) :
    let P := completeMomentPrices n Q O Sm SM C σ H
    (gaussMat (mA n) (mA n) (tA n)).real
      (⋃ i, momentBad ν (fun g => originalFourErrors (mkR wr (X, 0)) i (node g))
        (biasOrder i) (A i)) ≤
      P 0 / A 0 ^ 24 + P 1 / A 1 ^ 16 + P 2 / A 2 ^ 18 + P 3 / A 3 ^ 16 := by
  have hRA := paperOriginalBias_weighted16 hn wr hc ν hmass node hs X
    hQ hO hSm hSM hC hOp hE hcap hmin hmax hgap hk
  refine four_bias_markov_prices ν (gaussMat (mA n) (mA n) (tA n))
    (fun i g => originalFourErrors (mkR wr (X, 0)) i (node g))
    (completeMomentPrices n Q O Sm SM C σ H) A ?_
    (completeMomentPrices_nonneg _ _ _ _ _ _ _ _) hA ?_
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors _ i (node g)
  · intro i
    fin_cases i
    · exact originalLocationFluct_weighted24 (by omega) (mkR wr (X, 0)) ν node hs hO hOp hH h12
    · exact hRA.1
    · exact originalEnergyFluct_weighted18 (by omega) (mkR wr (X, 0)) ν node hs hO hOp
        hσ hH hQ hcap htrace h12
    · exact hRA.2

#print axioms four_bias_markov_prices
#print axioms paperOriginalFour_markov

/-- One first-layer event supplies all four original-matrix Markov bounds.
The operator and variance bounds are separate retained-data premises. -/
theorem paperOriginalFour_supply {n J : ℕ}
    (hn : 8000 ≤ n) (hn' : n ≤ 16384) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {Q O Sm SM σ H : ℝ}
    (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 < Sm) (hSM : 0 ≤ SM)
    (hσ : 0 ≤ σ) (hH : 0 ≤ H)
    (hcap : ∀ g, 1 - nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ Q)
    (hgap : 0 < envelopeGap n Q O Sm)
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS (mkR wr (0, 0)) (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12))
    (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) :
    ∃ E : Set (Matrix (Fin (mA n)) (Fin n) ℝ),
      (gaussMat (mA n) n (2 / (n : ℝ))).real Eᶜ ≤ 1 / 10000 ∧
      ∀ X ∈ E, OpB X O →
        (∀ g, Sm ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g))) →
        (∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤ SM) →
        (∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤
          σ ^ 2 * (1 - nodeS (mkR wr (0, 0)) (node g) ^ 2)) →
        let P := completeMomentPrices n Q O Sm SM
          (statisticsConstant (paperBound256 n)) σ H
        (gaussMat (mA n) (mA n) (tA n)).real
          (⋃ i, momentBad ν (fun g => originalFourErrors (mkR wr (X, 0)) i (node g))
            (biasOrder i) (A i)) ≤
          P 0 / A 0 ^ 24 + P 1 / A 1 ^ 16 + P 2 / A 2 ^ 18 + P 3 / A 3 ^ 16 := by
  refine ⟨paperRegularStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)),
    paperRegularStatisticsEvent_oneTenThousand hn hn' wr hc ν hmass node hs, ?_⟩
  intro X hX hOp hmin hmax htrace
  have hC : 0 ≤ statisticsConstant (paperBound256 n) :=
    (statisticsConstant_pos
      ((paperStatisticsBound_pos (by omega : 4 ≤ n) (by norm_num : 1 ≤ 2)).trans_le
        (paperStatisticsBound_le_paperBound hn hn'))).le
  exact paperOriginalFour_markov (by omega) wr hc ν hmass node hs X
    hQ hO hSm hSM hC hσ hH hOp hX.1 hcap hmin hmax htrace hgap h12 hX.2 A hA

#check paperOriginalFour_supply
#print axioms paperOriginalFour_supply
end BstLean.Part223
