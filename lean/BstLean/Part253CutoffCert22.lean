import BstLean.Part253CutoffData

/-! Each cell rejects every cutoff in the fixed order-twenty-four formula. -/
namespace BstLean.Part253
open Real

theorem allCutoffsCell22 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 22) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 22 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 22) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.262249275 : ℝ)) (d1 := (0.267249275 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8328630587043 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8555927212173 : ℝ)) (q := (0.0210439284999 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8328630587043 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8526657637082 : ℝ)) (q := (0.0181169709908 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell23 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 23) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 23 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 23) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.262745854 : ℝ)) (d1 := (0.267745854 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8325170701611 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8553024760867 : ℝ)) (q := (0.0210996719125 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8325170701611 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8523745219093 : ℝ)) (q := (0.0181717177351 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell24 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 24) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 24 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 24) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.263916104 : ℝ)) (d1 := (0.268916104 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8321713254590 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8546180875690 : ℝ)) (q := (0.0207610280969 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8321713254590 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8516877805863 : ℝ)) (q := (0.0178307211142 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell25 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 25) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 25 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 25) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.264412686 : ℝ)) (d1 := (0.269412686 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8318258242682 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8543275095653 : ℝ)) (q := (0.0208159512840 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8318258242682 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8513962024816 : ℝ)) (q := (0.0178846442003 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell26 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 26) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 26 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 26) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.264909269 : ℝ)) (d1 := (0.269909269 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8314805662608 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8540368321098 : ℝ)) (q := (0.0208705318359 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8314805662608 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8511045238983 : ℝ)) (q := (0.0179382236244 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell27 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 27) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 27 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 27) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.265405853 : ℝ)) (d1 := (0.270405853 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8311355511103 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8537460551007 : ℝ)) (q := (0.0209247699773 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8311355511103 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8508127447330 : ℝ)) (q := (0.0179914596096 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

end BstLean.Part253
