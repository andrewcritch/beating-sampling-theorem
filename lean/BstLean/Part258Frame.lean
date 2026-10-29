import BstLean.Part258Covariance
import BstLean.Part256Supply

/-! The changed final cap fits the unchanged frame allowance. -/
namespace BstLean.Part258
open Real Set BstLean.Part255
open BstLean.Part253 (retunedCentre centreGroup retunedCutoff massTable needed)

theorem scalarNeeded (j : Fin 43) :
    0 ≤ localCapTable (sourceIndex j) ∧
    (localCapTable (sourceIndex j) + retunedCentre (centreGroup (sourceIndex j))) /
      retunedCutoff (sourceIndex j) + massTable (sourceIndex j) ≤
        BstLean.Part249.optionBAgentFrame := by
  rw [localCapTable_source]
  by_cases hj : j.val = 42
  · have he : j = ⟨42, by decide⟩ := Fin.ext hj
    subst j
    norm_num [cap, lastCap, sourceIndex, retunedCentre, BstLean.Part253.centreTable,
      centreGroup, retunedCutoff, BstLean.Part253.cutoffTable, massTable,
      BstLean.Part249.optionBAgentFrame]
  · rw [cap, if_neg hj]
    have h := BstLean.Part256.scalarNeeded j
    rw [BstLean.Part255.localCapTable_source] at h
    exact h

theorem scalar_on_needed {i : Fin 60} (hi : needed i) :
    0 ≤ localCapTable i ∧
    (localCapTable i + retunedCentre (centreGroup i)) / retunedCutoff i + massTable i ≤
      BstLean.Part249.optionBAgentFrame := by
  obtain ⟨j, rfl⟩ := BstLean.Part255.needed_has_index i hi
  exact scalarNeeded j

theorem margin10 :
    (2680192/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((localCapTable (10 : Fin 60) + retunedCentre (centreGroup 10)) /
        retunedCutoff 10 + massTable 10) := by
  have hc : localCapTable (10 : Fin 60) =
      BstLean.Part255.localCapTable (10 : Fin 60) := by
    change localCapTable (sourceIndex ⟨0, by decide⟩) =
      BstLean.Part255.localCapTable (sourceIndex ⟨0, by decide⟩)
    rw [localCapTable_source, BstLean.Part255.localCapTable_source]
    rfl
  rw [hc]
  exact BstLean.Part256.margin10.1

theorem margin52 :
    (49255/10^6 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((localCapTable (52 : Fin 60) + retunedCentre (centreGroup 52)) /
        retunedCutoff 52 + massTable 52) := by
  change (49255/10^6 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((localCapTable (sourceIndex ⟨42, by decide⟩) + retunedCentre (centreGroup 52)) /
        retunedCutoff 52 + massTable 52)
  rw [localCapTable_source]
  norm_num [cap, lastCap, retunedCentre, BstLean.Part253.centreTable, centreGroup,
    retunedCutoff, BstLean.Part253.cutoffTable, massTable,
    BstLean.Part249.optionBAgentFrame]

theorem supplied_cell_subset {i : Fin 60} {θ : ℝ} (hm : θ ∈ cell i) :
    θ ∈ BstLean.Part253.cell i := by
  have h := cell_source hm
  simpa only [sourceCell, sourceLower, sourceUpper, BstLean.Part251.noiseNode,
    BstLean.Part251.proposedThetaUpper, BstLean.Part253.cell,
    BstLean.Part253.noiseNode] using h

noncomputable def selectedFrameInputs {c : BstLean.Part157.Ret 12225} {i : Fin 60}
    (hi : needed i)
    (hm : BstLean.Part150.thetaC c.1.2
      ((BstLean.Part169.paperDesignP 12225).tau0 c) ∈ cell i)
    (F : BstLean.Part253.SourceEvents c) :
    BstLean.Part256.LocalFrameInputs (selected parameters payment) cell localCapTable c
      BstLean.Part249.optionBAgentFrame :=
  BstLean.Part256.frameInputs_from_retuned_network_general localCov hi hm
    (BstLean.Part253.retuned_network_from_events hi (supplied_cell_subset hm) F)
    (scalar_on_needed hi).1 (scalar_on_needed hi).2

end BstLean.Part258
