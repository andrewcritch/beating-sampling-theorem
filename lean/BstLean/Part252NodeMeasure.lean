import BstLean.Part252FourTable
import BstLean.Part223CompleteCharge

/-! The weighted node measure is the image of the original input-index
distribution. Its four moments supply the actual table event. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223

noncomputable def tableNodeIndex (wr : WRet 12225) (a : Ix 12225) : Fin (Js 12225) :=
  ⟨gW wr a, gIdx_lt _ (by norm_num) _⟩

theorem tableNodeIndex_measurable (wr : WRet 12225) : Measurable (tableNodeIndex wr) := by
  apply measurable_to_countable'
  intro k
  convert (measurable_gIdx_lat (mkR wr 0)) (measurableSet_singleton k.val) using 1
  ext a
  simp [tableNodeIndex, gW, Fin.ext_iff]

noncomputable def tableNodeMeasure (wr : WRet 12225) : Measure (Fin (Js 12225)) :=
  (muI 12225).map (tableNodeIndex wr)

theorem tableNodeMeasure_mass (wr : WRet 12225) : tableNodeMeasure wr univ = 1 := by
  rw [tableNodeMeasure, Measure.map_apply (tableNodeIndex_measurable wr) MeasurableSet.univ]
  simp

theorem actualFour_node_lintegral (c : Ret 12225) (i : Fin 4) :
    (∫⁻ a, ENNReal.ofReal (|actualFourError c i a| ^ biasOrder i) ∂muI 12225) =
      ∫⁻ g, ENNReal.ofReal (|originalFourErrors c i g.val (A2 c)| ^ biasOrder i)
        ∂tableNodeMeasure c.1 := by
  rw [tableNodeMeasure, lintegral_map (measurable_of_finite _)
    (tableNodeIndex_measurable c.1)]
  rfl

theorem fourTableMoments_of_nodeMoments (c : Ret 12225)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    FourTableMoments c := by
  refine ⟨fun i => ⟨?_, (h i).nonneg, ?_⟩⟩
  · have hf : actualFourError c i = (fun g : Fin (Js 12225) =>
        originalFourErrors c i g.val (A2 c)) ∘ tableNodeIndex c.1 := rfl
    rw [hf]
    exact (h i).measurable.comp (tableNodeIndex_measurable c.1)
  · rw [actualFour_node_lintegral]
    exact (h i).moment

theorem tableEvent_of_nodeMoments (c : Ret 12225)
    (h : ∀ i, MomentBound (tableNodeMeasure c.1) (biasOrder i)
      (fun g => originalFourErrors c i g.val (A2 c)) (fourAllowances i)) :
    c ∈ tableEvent :=
  fourTableMoments_to_event (fourTableMoments_of_nodeMoments c h)

theorem tableEvent_of_second_layer_good (c : Ret 12225)
    (M : Matrix (Fin (mA 12225)) (Fin (mA 12225)) ℝ)
    (h : M ∉ ⋃ i, momentBad (tableNodeMeasure c.1)
      (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i)) :
    withA2 c M ∈ tableEvent := by
  apply tableEvent_of_nodeMoments
  intro i
  refine ⟨measurable_of_finite _, ?_, ?_⟩
  · fin_cases i <;> norm_num [fourAllowances]
  · have hi : M ∉ momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) :=
      fun hm => h (mem_iUnion.mpr ⟨i, hm⟩)
    exact le_of_not_gt hi

theorem table_second_layer_charge (c : Ret 12225) (P : Fin 4 → ℝ)
    (hP : ∀ i, 0 ≤ P i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ M,
      ENNReal.ofReal (|originalFourErrors c i g.val M| ^ biasOrder i)
        ∂gaussMat (mA 12225) (mA 12225) (tA 12225) ∂tableNodeMeasure c.1 ≤
          ENNReal.ofReal (P i)) :
    (gaussMat (mA 12225) (mA 12225) (tA 12225)).real
      {M | withA2 c M ∉ tableEvent} ≤
        P 0 / fourAllowances 0 ^ 24 + P 1 / fourAllowances 1 ^ 16 +
        P 2 / fourAllowances 2 ^ 18 + P 3 / fourAllowances 3 ^ 16 := by
  have hs : {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
    intro M hM
    by_contra hg
    exact hM (tableEvent_of_second_layer_good c M hg)
  refine (measureReal_mono hs (measure_ne_top _ _)).trans ?_
  apply four_bias_markov_prices _ _ _ P fourAllowances _ hP _ hM
  · intro i
    apply measurable_from_prod_countable_right
    intro g
    exact measurable_originalFourErrors c i g.val
  · intro i
    fin_cases i <;> norm_num [fourAllowances]

theorem table_second_layer_bad_subset (c : Ret 12225) :
    {M | withA2 c M ∉ tableEvent} ⊆
      ⋃ i, momentBad (tableNodeMeasure c.1)
        (fun g => originalFourErrors c i g.val) (biasOrder i) (fourAllowances i) := by
  intro M hM
  by_contra hg
  exact hM (tableEvent_of_second_layer_good c M hg)

end BstLean.Part252
