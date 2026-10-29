import BstLean.Part292BiasSupply
import BstLean.Part292BiasScale
import BstLean.Part292CoefficientCaps
import BstLean.Part292TraceSupply

/-! The conditional order-104 bias supplier uses the original second Agent matrix. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part220 BstLean.Part223

noncomputable def lowRowData {n : ℕ} (wr : WRet n) (g : ℕ)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ) : RAData :=
  let M := fun i => paperNodeStatistic wr g i A
  latitudeRAData (1-nodeS (mkR wr (0,0)) g^2) (lowSigma n) (lowBiasUpper n)
    (basePlane n (M 0) (M 1)) (baseVariance n (M 2))
    (baseExceptionalCoefficient n (lowOperator n) (lowSigma n)*(M 2)^4)

theorem originalBias_band {n J : ℕ} (hn : 8000 ≤ n) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν Set.univ ≤ 1) (node : Fin J → ℕ)
    (hgeo : ∀ g, 0 ≤ nodeS (mkR wr (0,0)) (node g) ∧
      391/1000 ≤ 1-nodeS (mkR wr (0,0)) (node g)^2 ∧
      1-nodeS (mkR wr (0,0)) (node g)^2 ≤ 605/1000)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (hop : OpB A (lowOperator n))
    (hlow : A ∈ traceLow (BstLean.Part161.uHat (mkR wr (0,0))))
    (hhigh : A ∈ traceHigh (BstLean.Part161.uHat (mkR wr (0,0))))
    (hevent : A ∈ BstLean.Part239.node416Event wr ν node (517/200))
    (hkink : ∀ g, ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n-1)), ∀ j,
      (A *ᵥ BstLean.Part161.xLat (mkR wr (0,0)) (nodeS (mkR wr (0,0)) (node g))
        (BstLean.Part53.unitF53 v)) j ≠ 0) :
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalLocationBias (mkR wr (A,0)) (node g) M|^104)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal ((635/100000 : ℝ)^104) ∧
    (∫⁻ g, ∫⁻ M, ENNReal.ofReal (|originalEnergyBias (mkR wr (A,0)) (node g) M|^104)
      ∂gaussMat (mA n) (mA n) (tA n) ∂ν) ≤ ENNReal.ofReal ((575/100000 : ℝ)^104) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd : 0 < (n : ℝ)-2 := by linarith
  have hσ : 0 < lowSigma n := by unfold lowSigma; positivity
  have hsp : 0 ≤ lowBiasUpper n := by unfold lowBiasUpper; positivity
  have hO : 0 ≤ lowOperator n := by unfold lowOperator; positivity
  have ht := tA_nonneg n
  have hInv := (inverseRadius8_pos (by omega : 8 < n-1)).le
  have hgap : 0 < baseGap n (lowOperator n) (lowSigma n) :=
    lt_of_lt_of_le (by positivity) (low_gap_cap hn)
  let M := fun g i => paperNodeStatistic wr (node g) i A
  let D := fun g => basePlane n (M g 0) (M g 1)
  let V := fun g => baseVariance n (M g 2)
  let P := fun g => baseExceptionalCoefficient n (lowOperator n) (lowSigma n)*(M g 2)^4
  have hM0 g i : 0 ≤ M g i := paperNodeStatistic_nonneg _ _ _ _
  have hD0 g : 0 ≤ D g := by
    have h0 := hM0 g 0
    have h1 := hM0 g 1
    dsimp [D, basePlane]
    positivity
  have hV0 g : 0 ≤ V g := by
    have h2 := hM0 g 2
    dsimp [V, baseVariance]
    positivity
  have hP0 g : 0 ≤ P g := by dsimp [P, baseExceptionalCoefficient]; positivity
  have hbase := base_statistics_moments (O := lowOperator n) (σ := lowSigma n)
    (by omega : 10 ≤ n) wr ν node A hevent
  have hD : MomentBound ν 416 D ((1035/100 : ℝ)/(n : ℝ)^3) :=
    momentBound_weaken hbase.1 (base_plane_cap hn)
  have hV : MomentBound ν 416 V ((414/10 : ℝ)/(n : ℝ)^4) :=
    momentBound_weaken hbase.2.1 (base_variance_cap hn)
  have hP : MomentBound ν 104 P ((8*10^14 : ℝ)/(n : ℝ)^8) :=
    momentBound_weaken hbase.2.2 (base_exceptional_cap hn)
  have hcoeff := latitude_coefficient_moments n ν hmass
    (fun g => 1-nodeS (mkR wr (0,0)) (node g)^2) D V P hD hV hP hD0 hV0 hP0
    (by norm_num : (0 : ℝ) < 391/1000) (fun g => (hgeo g).2.1)
    (fun g => (hgeo g).2.2) (by norm_num) hσ hsp hO
  have hs g : nodeS (mkR wr (A,0)) (node g)^2 ≤ 1 := by
    have h := (hgeo g).2.1
    change nodeS (mkR wr (0,0)) (node g)^2 ≤ 1
    linarith
  have hstat g : NodeStat (mkR wr (A,0)) (node g)
      (lowRowData wr (node g) A).Smin (lowRowData wr (node g) A).Smax
      (lowRowData wr (node g) A).D (lowRowData wr (node g) A).H
      (lowRowData wr (node g) A).V (lowRowData wr (node g) A).P := by
    apply latitudeNodeStat (by omega) wr hc (node g) A hO hop
      (by linarith [(hgeo g).2.1])
    · exact variance_lower_low hn (mkR wr (A,0)) hc hlow (hgeo g).1 (hs g)
    · exact variance_bias_upper_low hn (mkR wr (A,0)) hc hhigh (hs g) (hgeo g).2.2
    · exact hgap
    · exact hkink g
  have hSm g : 0 < (lowRowData wr (node g) A).Smin := by
    change 0 < (1-nodeS (mkR wr (0,0)) (node g)^2)*lowSigma n^2
    exact mul_pos (by linarith [(hgeo g).2.1]) (sq_pos_of_pos hσ)
  have hb := originalBias_weighted104 (by omega) (mkR wr (A,0)) ν node hs hO hop
    (fun g => lowRowData wr (node g) A) hSm hstat
    hcoeff.1 hcoeff.2.1 hcoeff.2.2.1 hcoeff.2.2.2.1 hcoeff.2.2.2.2.1 hcoeff.2.2.2.2.2
  have hcap := normalized_coefficient_caps hn
  exact ⟨hb.1.trans (ENNReal.ofReal_le_ofReal (location_price_normalized hn
      hcoeff.1.nonneg hcoeff.2.1.nonneg hcoeff.2.2.1.nonneg hcap.1 hcap.2.1 hcap.2.2.1)),
    hb.2.trans (ENNReal.ofReal_le_ofReal (energy_price_normalized hn
      hcoeff.2.2.2.1.nonneg hcoeff.2.2.2.2.1.nonneg hcoeff.2.2.2.2.2.nonneg
      hcap.2.2.2.1 hcap.2.2.2.2.1 hcap.2.2.2.2.2))⟩

end BstLean.Part292

/-- info: 'BstLean.Part292.originalBias_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.originalBias_band
