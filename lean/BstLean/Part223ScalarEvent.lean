import BstLean.Part223NodeSupply
import BstLean.Part223PaperEvent

/-! The scalar node supply adds no charge to the weighted statistics event. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part171
open BstLean.Part170 (mkR)
open BstLean.Part220 (statisticsConstant)

def paperNodeSupplyEvent {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (C O : ℝ) (Sm SM : Fin J → ℝ) :
    Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | A ∈ paperStatisticsEvent wr ν node C ∧ (OpB A O → ∀ g,
    Sm g ≤ vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) (node g)) →
    vsig2 (mkR wr (A, 0)) (nodeS (mkR wr (A, 0)) (node g)) ≤ SM g →
    let s := nodeS (mkR wr (0, 0)) (node g)
    let M := fun i => paperNodeStatistic wr (node g) i A
    NodeStat (mkR wr (A, 0)) (node g) (Sm g) (SM g)
      (paperPlaneBound n s (M 0) (M 1)) (paperPlaneBound n s (M 0) (M 1))
      (paperVarianceBound n s (M 0) (M 1) (M 2))
      (paperExceptionalBound n s O (Sm g) (M 2)))}

/-- The scalar transfer changes the weighted event only on a null set. -/
theorem paperNodeSupplyEvent_ae {n J : ℕ} (hn : 10 ≤ n) (wr : WRet n)
    (hc : wr.2 ≠ 0) (ν : Measure (Fin J)) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    (C : ℝ) {O : ℝ} (hO : 0 ≤ O) (Sm SM : Fin J → ℝ)
    (hgap : ∀ g, 0 < Sm g / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) (node g)) O) :
    paperNodeSupplyEvent wr ν node C O Sm SM =ᵐ[gaussMat (mA n) n (2 / (n : ℝ))]
      paperStatisticsEvent wr ν node C := by
  filter_upwards [nodeStat_of_paperStatistics_ae hn wr hc node hs hO Sm SM hgap] with A hA
  apply propext
  change (_ ∧ _) ↔ _
  exact ⟨And.left, fun h => ⟨h, hA⟩⟩

/-- The three weighted norms and their scalar node consequences cost one ten-thousandth.
The operator and variance events remain distinct retained-data inputs. -/
theorem paperNodeSupplyEvent_oneTenThousand {n J : ℕ}
    (hn : 8000 ≤ n) (hn' : n ≤ 16384) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1)
    {O : ℝ} (hO : 0 ≤ O) (Sm SM : Fin J → ℝ)
    (hgap : ∀ g, 0 < Sm g / 2 - planeTraceCap n (nodeS (mkR wr (0, 0)) (node g)) O) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (paperNodeSupplyEvent wr ν node (statisticsConstant (paperBound256 n)) O Sm SM)ᶜ ≤
        1 / 10000 := by
  have he := paperNodeSupplyEvent_ae (by omega : 10 ≤ n) wr hc ν node hs
    (statisticsConstant (paperBound256 n)) hO Sm SM hgap
  have hec : (paperNodeSupplyEvent wr ν node (statisticsConstant (paperBound256 n)) O Sm SM)ᶜ
      =ᵐ[gaussMat (mA n) n (2 / (n : ℝ))]
        (paperStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)))ᶜ := by
    filter_upwards [he] with A hA
    exact congrArg Not hA
  have hm := congrArg ENNReal.toReal (measure_congr hec)
  change _ ≤ _
  rw [measureReal_def, hm]
  exact paperCoefficient_statistics_oneTenThousand hn hn' wr hc ν hmass node hs

#print axioms paperNodeSupplyEvent_ae
#print axioms paperNodeSupplyEvent_oneTenThousand

def paperRegularStatisticsEvent {n J : ℕ} (wr : WRet n) (ν : Measure (Fin J))
    (node : Fin J → ℕ) (C : ℝ) : Set (Matrix (Fin (mA n)) (Fin n) ℝ) :=
  {A | A ∈ paperStatisticsEvent wr ν node C ∧ ∀ g,
    ∀ᵐ v ∂BstLean.Part29.stdGauss (Fin (n - 1)),
      ∀ j, (A *ᵥ BstLean.Part161.xLat (mkR wr (0, 0))
        (nodeS (mkR wr (0, 0)) (node g)) (BstLean.Part53.unitF53 v)) j ≠ 0}

theorem paperRegularStatisticsEvent_ae {n J : ℕ} (hn : 2 ≤ n) (wr : WRet n)
    (ν : Measure (Fin J)) (node : Fin J → ℕ) (C : ℝ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    paperRegularStatisticsEvent wr ν node C =ᵐ[gaussMat (mA n) n (2 / (n : ℝ))]
      paperStatisticsEvent wr ν node C := by
  filter_upwards [paperNodes_kink_ae hn wr node hs] with A hA
  apply propext
  change (_ ∧ _) ↔ _
  exact ⟨And.left, fun h => ⟨h, hA⟩⟩

/-- The regularity premises of the complete supply cost no additional probability. -/
theorem paperRegularStatisticsEvent_oneTenThousand {n J : ℕ}
    (hn : 8000 ≤ n) (hn' : n ≤ 16384) (wr : WRet n) (hc : wr.2 ≠ 0)
    (ν : Measure (Fin J)) [SFinite ν] (hmass : ν univ ≤ 1) (node : Fin J → ℕ)
    (hs : ∀ g, nodeS (mkR wr (0, 0)) (node g) ^ 2 ≤ 1) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real
      (paperRegularStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)))ᶜ ≤
        1 / 10000 := by
  have he := paperRegularStatisticsEvent_ae (by omega : 2 ≤ n) wr ν node
    (statisticsConstant (paperBound256 n)) hs
  have hec : (paperRegularStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)))ᶜ
      =ᵐ[gaussMat (mA n) n (2 / (n : ℝ))]
        (paperStatisticsEvent wr ν node (statisticsConstant (paperBound256 n)))ᶜ := by
    filter_upwards [he] with A hA
    exact congrArg Not hA
  rw [measureReal_def, congrArg ENNReal.toReal (measure_congr hec)]
  exact paperCoefficient_statistics_oneTenThousand hn hn' wr hc ν hmass node hs

#print axioms paperRegularStatisticsEvent_ae
#print axioms paperRegularStatisticsEvent_oneTenThousand
end BstLean.Part223
