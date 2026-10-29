import BstLean.Part253Data

/-! Exact rational cell data and certificates. -/
namespace BstLean.Part253
open Real Set

theorem scalarCell22 : ScalarCertificate 22 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83286305870432 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374433032 : ℝ))
      (E := energyTable 22) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 22)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83286305870432 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374433032 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell23 : ScalarCertificate 23 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83251707016118 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374414188 : ℝ))
      (E := energyTable 23) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 23)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83251707016118 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374414188 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell24 : ScalarCertificate 24 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83217132545907 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374435519 : ℝ))
      (E := energyTable 24) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 24)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83217132545907 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374435519 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell25 : ScalarCertificate 25 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83182582426828 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374442824 : ℝ))
      (E := energyTable 25) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 25)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83182582426828 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374442824 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell26 : ScalarCertificate 26 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83148056626083 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374439967 : ℝ))
      (E := energyTable 26) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 26)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83148056626083 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374439967 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]

theorem scalarCell27 : ScalarCertificate 27 := by
  constructor
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]
  · have h := gap_lower (a := (0.83113555111038 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374430580 : ℝ))
      (E := energyTable 27) (xi := parallelCap) (u := radiusCutoff) (d := cutoffTable 27)
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num)
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (a := (0.83113555111038 : ℝ)) (b := (0.00168573401311 : ℝ)) (q := (0.02304374430580 : ℝ))
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]) (by norm_num) (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame])
      (by norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame, rotationPowerCap])
  · norm_num [capTable, centreTable, centreGroup, cutoffTable, energyTable, directionCap, parallelCap, energyCap, massTable, radiusCutoff, BstLean.Part249.optionBAgentFrame]


end BstLean.Part253
