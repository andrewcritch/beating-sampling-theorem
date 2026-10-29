import BstLean.Part255Covariance
import BstLean.Part253RetunedScalar

namespace BstLean.Part256
open BstLean.Part253

theorem margin52 : (49263493/10^9 : ℝ) ≤ BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (52 : Fin 60) + retunedCentre (centreGroup 52)) /
        retunedCutoff 52 + massTable 52) ∧
    BstLean.Part249.optionBAgentFrame -
      ((BstLean.Part255.localCapTable (52 : Fin 60) + retunedCentre (centreGroup 52)) /
        retunedCutoff 52 + massTable 52) < (49263494/10^9 : ℝ) := by
  have hcap : BstLean.Part255.localCapTable (52 : Fin 60) = (291823659/1000000000 : ℝ) := by
    change BstLean.Part255.localCapTable (BstLean.Part255.sourceIndex ⟨42, by decide⟩) = _
    rw [BstLean.Part255.localCapTable_source]
    norm_num [BstLean.Part255.localCap]
  rw [hcap]
  norm_num [retunedCentre, centreTable, centreGroup,
    retunedCutoff, cutoffTable, massTable, BstLean.Part249.optionBAgentFrame]

end BstLean.Part256
