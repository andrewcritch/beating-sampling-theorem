import BstLean.Part255Covariance
import BstLean.Part253RetunedScalar

namespace BstLean.Part256
open BstLean.Part253

theorem margin10 : (2680192/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (10 : Fin 60) + retunedCentre (centreGroup 10)) /
        retunedCutoff 10 + massTable 10) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (10 : Fin 60) + retunedCentre (centreGroup 10)) /
        retunedCutoff 10 + massTable 10) < (2680193/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (10 : Fin 60) = (137976367/500000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨0, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

theorem margin11 : (4534367/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (11 : Fin 60) + retunedCentre (centreGroup 11)) /
        retunedCutoff 11 + massTable 11) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (11 : Fin 60) + retunedCentre (centreGroup 11)) /
        retunedCutoff 11 + massTable 11) < (4534368/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (11 : Fin 60) = (138178003/500000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨1, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

theorem margin12 : (2515343/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (12 : Fin 60) + retunedCentre (centreGroup 12)) /
        retunedCutoff 12 + massTable 12) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (12 : Fin 60) + retunedCentre (centreGroup 12)) /
        retunedCutoff 12 + massTable 12) < (2515344/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (12 : Fin 60) = (276758283/1000000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨2, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

theorem margin13 : (4361318/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (13 : Fin 60) + retunedCentre (centreGroup 13)) /
        retunedCutoff 13 + massTable 13) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (13 : Fin 60) + retunedCentre (centreGroup 13)) /
        retunedCutoff 13 + massTable 13) < (4361319/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (13 : Fin 60) = (277159561/1000000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨3, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

theorem margin14 : (6198659/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (14 : Fin 60) + retunedCentre (centreGroup 14)) /
        retunedCutoff 14 + massTable 14) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (14 : Fin 60) + retunedCentre (centreGroup 14)) /
        retunedCutoff 14 + massTable 14) < (6198660/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (14 : Fin 60) = (277559849/1000000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨4, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

theorem margin15 : (8027444/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (15 : Fin 60) + retunedCentre (centreGroup 15)) /
        retunedCutoff 15 + massTable 15) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (15 : Fin 60) + retunedCentre (centreGroup 15)) /
        retunedCutoff 15 + massTable 15) < (8027445/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (15 : Fin 60) = (55591829/200000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨5, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

end BstLean.Part256
