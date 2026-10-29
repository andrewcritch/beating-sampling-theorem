import BstLean.Part253CutoffData

/-! Each cell rejects every cutoff in the fixed order-twenty-four formula. -/
namespace BstLean.Part253
open Real

theorem allCutoffsCell28 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 28) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 28 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 28) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.265902439 : ℝ)) (d1 := (0.270902439 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8307907784923 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8534551778507 : ℝ)) (q := (0.0209786653453 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8307907784923 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8505208642944 : ℝ)) (q := (0.0180443517890 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell29 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 29) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 29 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 29) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.266399026 : ℝ)) (d1 := (0.271399026 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8304462480836 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8531642008430 : ℝ)) (q := (0.0210322187463 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8304462480836 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8502288830663 : ℝ)) (q := (0.0180969009696 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell30 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 30) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 30 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 30) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.267575400 : ℝ)) (d1 := (0.272575400 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8301019595630 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8524745037830 : ℝ)) (q := (0.0206868102069 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8301019595630 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8495368029698 : ℝ)) (q := (0.0177491093937 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell31 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 31) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 31 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 31) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.268071990 : ℝ)) (d1 := (0.273071990 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8297579126109 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8521831901652 : ℝ)) (q := (0.0207395435412 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8297579126109 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8492444816424 : ℝ)) (q := (0.0178008350184 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell32 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 32) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 32 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 32) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.268568581 : ℝ)) (d1 := (0.273568581 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8294141069091 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8518917763426 : ℝ)) (q := (0.0207919354204 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8294141069091 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8489520590705 : ℝ)) (q := (0.0178522181483 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

theorem allCutoffsCell33 {d : ℝ} (hd : 0 < d)
    (hgap : 0 < √((1 - radiusCutoff) ^ 2 - d) -
      (√(energyTable 33) + √(parallelCap / 12225))) :
    (1.4601 : ℝ) ≤ certifiedNumerator 33 / d +
      BstLean.Part222.massBoundOrder 12225 12 directionCap energyCap parallelCap
        (energyTable 33) radiusCutoff d := by
  apply cutoff_split_obstruction (d0 := (0.269065174 : ℝ)) (d1 := (0.274065174 : ℝ))
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) hd (by norm_num) (by norm_num) (by norm_num) hgap
    (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8290705421414 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8516002616252 : ℝ)) (q := (0.0208439854707 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
  · intro z hz hg
    apply mass_lower_rational (a := (0.8290705421414 : ℝ)) (b := (0.0016857340131 : ℝ))
      (w := (0.8486595345603 : ℝ)) (q := (0.0179032584058 : ℝ))
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])
      (by norm_num) (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor]) (by norm_num)
      (by norm_num [radiusCutoff]; linarith) (by norm_num) (by norm_num) hg
      (by norm_num [certifiedNumerator, BstLean.Part254.capTable, BstLean.Part254.gaussianCapAt, BstLean.Part254.Needed, centreTable, centreGroup, energyTable, directionCap, energyCap, parallelCap, radiusCutoff, rotationPowerFloor])

end BstLean.Part253
