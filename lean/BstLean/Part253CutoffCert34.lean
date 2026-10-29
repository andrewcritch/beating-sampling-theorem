import BstLean.Part253CutoffData

/-! Each cell rejects every cutoff in the fixed order-twenty-four formula. -/
namespace BstLean.Part253
open Real

theorem allCutoffsCell34 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 34) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 34 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 34) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.269561768 : ℝ)) (d1 := (0.274561768 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8287272179928 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8513086464967 : ℝ)) (q := (0.0208956944908 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8287272179928 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8483669085956 : ℝ)) (q := (0.0179539565897 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell35 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 35) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 35 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 35) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.270058362 : ℝ)) (d1 := (0.275058362 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8283841341503 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8510169314415 : ℝ)) (q := (0.0209470632781 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8283841341503 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8480741816611 : ℝ)) (q := (0.0180043134977 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell36 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 36) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 36 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 36) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.271243333 : ℝ)) (d1 := (0.276243333 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8280412903023 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8503204375999 : ℝ)) (q := (0.0205934132845 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8280412903023 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8473752690515 : ℝ)) (q := (0.0176482447361 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell37 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 37) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 37 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 37) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.271739931 : ℝ)) (d1 := (0.276739931 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8276986861387 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8500283810556 : ℝ)) (q := (0.0206439609038 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8276986861387 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8470821970742 : ℝ)) (q := (0.0176977769224 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell38 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 38) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 38 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 38) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.272236530 : ℝ)) (d1 := (0.277236530 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8273563213512 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8497362235424 : ℝ)) (q := (0.0206941681781 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8273563213512 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8467890230749 : ℝ)) (q := (0.0177469677106 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell39 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 39) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 39 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 39) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.272733131 : ℝ)) (d1 := (0.277733131 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8270141956329 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8494439643673 : ℝ)) (q := (0.0207440347213 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8270141956329 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8464957463568 : ℝ)) (q := (0.0177958167108 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

end BstLean.Part253
