import BstLean.Part292BiasBand
import BstLean.Part292Fluctuations
import BstLean.Part292Charge
import BstLean.Part292NodeMoment
import BstLean.Part223FourSupply

/-! All four actual moment suppliers use one first matrix and one original second matrix. -/
namespace BstLean.Part292
open MeasureTheory Real Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part170 BstLean.Part171
open BstLean.Part223

theorem originalFour_band {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n} (hw : tableWorldGuard wr)
    (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (hop : OpB A (lowOperator n))
    (hlow : A ∈ traceLow (BstLean.Part161.uHat (mkR wr (0,0))))
    (hhigh : A ∈ traceHigh (BstLean.Part161.uHat (mkR wr (0,0))))
    (hevent : A ∈ BstLean.Part239.node416Event wr
      (BstLean.Part280.nodeMeasureN (by omega) wr) Fin.val (517/200))
    (hkink : ∀ g : Fin (Js n), ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n-1)), ∀ j,
      (A *ᵥ BstLean.Part161.xLat (mkR wr (0,0)) (nodeS (mkR wr (0,0)) g.val)
        (BstLean.Part53.unitF53 v)) j ≠ 0) (i : Fin 4) :
    (∫⁻ g : Fin (Js n), ∫⁻ M, ENNReal.ofReal
      (|originalFourErrors (mkR wr (A,0)) i g.val M|^tableOrder i)
      ∂gaussMat (mA n) (mA n) (tA n)
      ∂BstLean.Part280.nodeMeasureN (by omega) wr) ≤ ENNReal.ofReal (momentCap i^tableOrder i) := by
  have hc := BstLean.Part172.sg_wr_ne (by omega : 1 ≤ n) hw.1
  have hgeo (g : Fin (Js n)) := node_geometry_low hn hw (0,0) g.isLt
  have hs (g : Fin (Js n)) : nodeS (mkR wr (A,0)) g.val^2 ≤ 1 := by
    change nodeS (mkR wr (0,0)) g.val^2 ≤ 1
    linarith [(hgeo g).2.1]
  have hB := originalBias_band hn wr hc (BstLean.Part280.nodeMeasureN (by omega) wr)
    (BstLean.Part280.nodeMeasureN_mass (by omega) wr).le Fin.val hgeo A hop hlow hhigh hevent hkink
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hσ : sqrt (n : ℝ)*lowUpperSigma n ≤ 2001/1000 := by
    unfold lowUpperSigma
    have he : sqrt (n : ℝ)*((2001/1000)/sqrt n) = 2001/1000 := by field_simp
    exact he.le
  have hF := originalFluctuations_band hn (mkR wr (A,0))
    (BstLean.Part280.nodeMeasureN (by omega) wr) Fin.val hs
    (by unfold lowOperator; positivity) hop (by unfold lowUpperSigma; positivity)
    (by norm_num : (0 : ℝ) ≤ 533/1000) (by norm_num : (0 : ℝ) ≤ 605/1000)
    (low_lambda_cap hn) hσ le_rfl le_rfl (fun g => (hgeo g).2.2)
    (fun g => variance_upper_low hn (mkR wr (A,0)) hc hhigh (hs g))
    (nodeMeasure_moment12_low hn hw)
  fin_cases i
  · exact hF.1
  · exact hB.1
  · exact hF.2
  · exact hB.2

theorem originalFour_markov_band {n : ℕ} (hn : 8000 ≤ n) {wr : WRet n}
    (hw : tableWorldGuard wr) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (hop : OpB A (lowOperator n))
    (hlow : A ∈ traceLow (BstLean.Part161.uHat (mkR wr (0,0))))
    (hhigh : A ∈ traceHigh (BstLean.Part161.uHat (mkR wr (0,0))))
    (hevent : A ∈ BstLean.Part239.node416Event wr
      (BstLean.Part280.nodeMeasureN (by omega) wr) Fin.val (517/200))
    (hkink : ∀ g : Fin (Js n), ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n-1)), ∀ j,
      (A *ᵥ BstLean.Part161.xLat (mkR wr (0,0)) (nodeS (mkR wr (0,0)) g.val)
        (BstLean.Part53.unitF53 v)) j ≠ 0) :
    (gaussMat (mA n) (mA n) (tA n))
      (tableBad (BstLean.Part280.nodeMeasureN (by omega) wr)
        (fun i g => originalFourErrors (mkR wr (A,0)) i g.val)) ≤
      ENNReal.ofReal (∑ i, (momentCap i/tableAllowance i)^tableOrder i) := by
  refine four_moment_charge _ _ _ _ ?_ momentCap_nonneg ?_
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors _ i g.val
  · exact originalFour_band hn hw A hop hlow hhigh hevent hkink

end BstLean.Part292
