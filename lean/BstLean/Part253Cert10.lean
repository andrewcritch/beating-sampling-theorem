import BstLean.Part253Data

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem scalarCell10 : ScalarCertificate 10 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83703406320110 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374436781 : ℝ))
      (E := energyTable 10) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 10)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83703406320110 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374436781 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell11 : ScalarCertificate 11 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83668512221539 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374406569 : ℝ))
      (E := energyTable 11) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 11)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83668512221539 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374406569 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell12 : ScalarCertificate 12 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83633642916367 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374405680 : ℝ))
      (E := energyTable 12) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 12)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83633642916367 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374405680 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell13 : ScalarCertificate 13 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83598798369498 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374441290 : ℝ))
      (E := energyTable 13) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 13)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83598798369498 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374441290 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell14 : ScalarCertificate 14 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83563978546021 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374404089 : ℝ))
      (E := energyTable 14) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 14)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83563978546021 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374404089 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell15 : ScalarCertificate 15 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83529183411204 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374416891 : ℝ))
      (E := energyTable 15) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 15)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83529183411204 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374416891 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]


end BstLean.Part253
