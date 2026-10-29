import BstLean.Part253Data

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem scalarCell40 : ScalarCertificate 40 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82667230867854 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374412818 : ℝ))
      (E := energyTable 40) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 40)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82667230867854 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374412818 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell41 : ScalarCertificate 41 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82633066018433 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374445317 : ℝ))
      (E := energyTable 41) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 41)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82633066018433 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374445317 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell42 : ScalarCertificate 42 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82598924984811 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374439154 : ℝ))
      (E := energyTable 42) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 42)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82598924984811 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374439154 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell43 : ScalarCertificate 43 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82564807736922 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374453033 : ℝ))
      (E := energyTable 43) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 43)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82564807736922 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374453033 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell44 : ScalarCertificate 44 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82530714244851 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374427892 : ℝ))
      (E := energyTable 44) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 44)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82530714244851 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374427892 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell45 : ScalarCertificate 45 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.82496644478836 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374422040 : ℝ))
      (E := energyTable 45) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 45)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.82496644478836 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374422040 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]


end BstLean.Part253
