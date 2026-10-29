import BstLean.Part253CutoffData

/-! Each cell rejects every cutoff in the fixed order-twenty-four formula. -/
namespace BstLean.Part253
open Real

theorem allCutoffsCell16 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 16) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 16 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 16) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.258600181 : ℝ)) (d1 := (0.263600181 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8349441293050 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8577225650524 : ℝ)) (q := (0.0210927017343 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8349441293050 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8548029004397 : ℝ)) (q := (0.0181730371216 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell17 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 17) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 17 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 17) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.259096753 : ℝ)) (d1 := (0.264096753 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8345966706954 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8574330449662 : ℝ)) (q := (0.0211506402577 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8345966706954 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8545123911331 : ℝ)) (q := (0.0182299864246 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell18 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 18) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 18 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 18) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.260262971 : ℝ)) (d1 := (0.265262971 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8342494579413 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8567527114635 : ℝ)) (q := (0.0208175195091 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8342494579413 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8538297304499 : ℝ)) (q := (0.0178945384955 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell19 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 19) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 19 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 19) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.260759545 : ℝ)) (d1 := (0.265759545 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8339024907026 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8564628623589 : ℝ)) (q := (0.0208746376432 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8339024907026 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8535388887450 : ℝ)) (q := (0.0179506640293 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell20 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 20) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 20 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 20) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.261256120 : ℝ)) (d1 := (0.266256120 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8335557686410 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8561729145448 : ℝ)) (q := (0.0209314118907 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8335557686410 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8532479473167 : ℝ)) (q := (0.0180064446626 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell21 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 21) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 21 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 21) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.261752697 : ℝ)) (d1 := (0.266752697 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8332092914199 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8558828673365 : ℝ)) (q := (0.0209878419035 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8332092914199 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8529569054765 : ℝ)) (q := (0.0180618800435 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

end BstLean.Part253
