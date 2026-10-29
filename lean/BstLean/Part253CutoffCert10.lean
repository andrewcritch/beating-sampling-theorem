import BstLean.Part253CutoffData

/-! Each cell rejects every cutoff in the fixed order-twenty-four formula. -/
namespace BstLean.Part253
open Real

theorem allCutoffsCell10 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 10) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 10 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 10) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.254953404 : ℝ)) (d1 := (0.259953404 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8370340632010 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8598457859408 : ℝ)) (q := (0.0211259887267 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8370340632010 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8569333554017 : ℝ)) (q := (0.0182135581876 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell11 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 11) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 11 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 11) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.255449967 : ℝ)) (d1 := (0.260449967 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8366851222153 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8595569862435 : ℝ)) (q := (0.0211861300151 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8366851222153 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8566435738393 : ℝ)) (q := (0.0182727176109 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell12 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 12) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 12 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 12) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.256613910 : ℝ)) (d1 := (0.261613910 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8363364291636 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8588796595566 : ℝ)) (q := (0.0208574963799 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8363364291636 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8559639417640 : ℝ)) (q := (0.0179417785873 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell13 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 13) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 13 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 13) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.257110475 : ℝ)) (d1 := (0.262110475 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8359879836949 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8585905337238 : ℝ)) (q := (0.0209168160158 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8359879836949 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8556738307323 : ℝ)) (q := (0.0180001130243 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell14 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 14) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 14 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 14) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.257607042 : ℝ)) (d1 := (0.262607042 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8356397854602 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8583013093315 : ℝ)) (q := (0.0209757898582 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8356397854602 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8553836201378 : ℝ)) (q := (0.0180581006645 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell15 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 15) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 15 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 15) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.258103611 : ℝ)) (d1 := (0.263103611 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8352918341120 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8580119862800 : ℝ)) (q := (0.0210344181549 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8352918341120 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8550933098792 : ℝ)) (q := (0.0181157417541 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

end BstLean.Part253
