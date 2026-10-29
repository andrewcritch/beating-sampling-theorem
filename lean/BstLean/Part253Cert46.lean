import BstLean.Part253Data

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem scalarCell46 : ScalarCertificate 46 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82462598409263 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374434799 : ℝ))
      (E := energyTable 46) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 46)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82462598409263 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374434799 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell47 : ScalarCertificate 47 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82428576006671 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374406376 : ℝ))
      (E := energyTable 47) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 47)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82428576006671 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374406376 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell48 : ScalarCertificate 48 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82394577241744 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374453415 : ℝ))
      (E := energyTable 48) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 48)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82394577241744 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374453415 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell49 : ScalarCertificate 49 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82360602085316 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374397837 : ℝ))
      (E := energyTable 49) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 49)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82360602085316 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374397837 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell50 : ScalarCertificate 50 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82326650508368 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374414841 : ℝ))
      (E := energyTable 50) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 50)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82326650508368 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374414841 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell51 : ScalarCertificate 51 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82292722482027 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374443746 : ℝ))
      (E := energyTable 51) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 51)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82292722482027 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374443746 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]


end BstLean.Part253
