import BstLean.Part253Data

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem scalarCell52 : ScalarCertificate 52 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82258817977563 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374423568 : ℝ))
      (E := energyTable 52) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 52)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82258817977563 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374423568 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]


end BstLean.Part253
