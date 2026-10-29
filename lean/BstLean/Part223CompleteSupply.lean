import BstLean.Part223EnvelopeMoments
import BstLean.Part223FourSupply
import BstLean.Part216NetworkWeighted

/-! Weighted original-network moments with all scalar statistics and row prices supplied. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Matrix Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170
open BstLean.Part220

variable {n J : ℕ}

theorem originalLocationFluct_weighted24 (hn : 3 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O H : ℝ} (hO : 0 ≤ O)
    (hOp : OpB (A1 c) O) (hH : 0 ≤ H)
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS c (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12)) :
    ∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalLocationFluct c (node g) M| ^ 24)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν ≤
      ENNReal.ofReal ((BstLean.Part216.k24 * (sqrt (n : ℝ) *
        sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) / 2) * sqrt H) ^ 24) := by
  have he (g : Fin J) :
      (∫⁻ M, ENNReal.ofReal (|originalLocationFluct c (node g) M| ^ 24)
        ∂gaussMat (mA n) (mA n) (tA n)) =
      ∫⁻ ξ₁, ∫⁻ ξ₂, ∫⁻ N,
        ENNReal.ofReal (|BstLean.Part216.locationPassFluct c (node g) ξ₁ ξ₂ N| ^ 24)
          ∂gaussMat (mA n) (mA n) (tA n) ∂stdGauss (Fin (mA n)) ∂stdGauss (Fin (mA n)) := by
    exact originalPlaneFluct_moment _ _ _
      (measurable_exFn_comp (measurable_withA2 c) measurable_const) 24
  simp_rw [he]
  exact BstLean.Part216.network_location24_weighted hn c ν node hs hO hOp hH h12

theorem originalEnergyFluct_weighted18 (hn : 3 ≤ n) (c : Ret n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS c (node g) ^ 2 ≤ 1) {O : ℝ} (hO : 0 ≤ O) (hOp : OpB (A1 c) O)
    {σ H Q : ℝ} (hσ : 0 ≤ σ) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hcap : ∀ g, 1 - nodeS c (node g) ^ 2 ≤ Q)
    (htrace : ∀ g, vsig2 c (nodeS c (node g)) ≤ σ ^ 2 * (1 - nodeS c (node g) ^ 2))
    (h12 : ∫⁻ g, ENNReal.ofReal ((1 - nodeS c (node g) ^ 2) ^ 12) ∂ν ≤
      ENNReal.ofReal (H ^ 12)) :
    ∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalEnergyFluct c (node g) M| ^ 18)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν ≤
      ENNReal.ofReal ((sqrt (tA n * (O ^ 2 / ((n : ℝ) - 2))) * σ *
        energyCoefficient18 n) ^ 18 * H ^ 12 * Q ^ 6) := by
  have he (g : Fin J) :
      (∫⁻ M, ENNReal.ofReal (|originalEnergyFluct c (node g) M| ^ 18)
        ∂gaussMat (mA n) (mA n) (tA n)) =
      ∫⁻ M, ENNReal.ofReal (|originalNetworkEnergyFluct c (node g) M| ^ 18)
        ∂(Measure.pi fun _ : Fin (mA n) => stdGauss (Fin (mA n))) := by
    rw [← scaledSecondLayer_distribution n]
    erw [lintegral_map ((measurable_originalEnergyFluct c (node g)).abs.pow_const 18
        |>.ennreal_ofReal) (measurable_const_smul (sqrt (tA n)))]
    simp_rw [originalEnergyFluct_scaled (by omega : 1 ≤ n)]
    rfl
  simp_rw [he]
  exact originalNetworkEnergy_weighted18 hn c ν node hs hO hOp hσ hH hQ hcap htrace h12

theorem paperOriginalBias_weighted16 (hn : 10 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (X : Matrix (Fin (mA n)) (Fin n) ℝ) {Q O Sm SM C : ℝ}
    (hQ : 0 ≤ Q) (hO : 0 ≤ O) (hSm : 0 < Sm) (hSM : 0 ≤ SM) (hC : 0 ≤ C)
    (hOp : OpB X O) (hE : X ∈ paperStatisticsEvent wr ν node C)
    (hcap : ∀ g, 1 - nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ Q)
    (hmin : ∀ g, Sm ≤ vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)))
    (hmax : ∀ g, vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) (node g)) ≤ SM)
    (hgap : 0 < envelopeGap n Q O Sm)
    (hk : ∀ g, ∀ᵐ v ∂stdGauss (Fin (n - 1)),
      ∀ j, (X *ᵥ BstLean.Part161.xLat (mkR wr (0, 0))
        (nodeS (mkR wr (0, 0)) (node g)) (BstLean.Part53.unitF53 v)) j ≠ 0) :
    let D := completeRAData (envelopeData n Q O Sm SM C C C) n O
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalLocationBias (mkR wr (X, 0)) (node g) M| ^ 16)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal (D.locationBound n O) ∧
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalEnergyBias (mkR wr (X, 0)) (node g) M| ^ 16)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal (D.energyBound n O) := by
  let d := fun g => envelopeData n Q O Sm SM
    (paperNodeStatistic wr (node g) 0 X) (paperNodeStatistic wr (node g) 1 X)
    (paperNodeStatistic wr (node g) 2 X)
  have hnode (g : Fin J) := originalBias_RA16_supply (by omega) (mkR wr (X, 0))
    (node g) (hs g) hO hOp (completeRAData (d g) n O)
      (completeRAData_supply _ _ hO (d g) hSm
        (envelopeNodeStat hn wr hc (node g) (hs g) X (hcap g) hO hOp
          (hmin g) (hmax g) hgap (hk g)))
  have hp := paperEvent_RA_prices hn wr hc ν hmass node hs X hQ hO hSm.le hSM hC hOp hE
  exact ⟨(lintegral_mono fun g => (hnode g).1).trans hp.1,
    (lintegral_mono fun g => (hnode g).2).trans hp.2⟩

#print axioms originalLocationFluct_weighted24
#print axioms originalEnergyFluct_weighted18
#print axioms paperOriginalBias_weighted16
end BstLean.Part223
