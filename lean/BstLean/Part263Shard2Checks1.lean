import BstLean.Part263Shard2Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12275_20 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20846271060399 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153896647381 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨20, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20846271060399 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153896647381 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_21 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83350465434847 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307797287219 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨21, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83350465434847 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307797287219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_22 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (2603620970537 / 3125000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (11539006457 / 500000000000 : ℝ))
      (E := (cell12275 ⟨22, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (2603620970537 / 3125000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (11539006457 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_23 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41640650537671 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461561050707 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨23, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41640650537671 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461561050707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_24 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83246755456229 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153904618089 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨24, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83246755456229 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153904618089 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_25 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83212234166923 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153906621693 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨25, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83212234166923 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153906621693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_26 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83177737174673 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461563444121 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨26, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83177737174673 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461563444121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_27 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (16628652889379 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576955307437 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨27, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (16628652889379 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576955307437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_28 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83108815951173 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153912607871 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨28, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83108815951173 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153912607871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_29 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83074391655257 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (28847865501 / 1250000000000 : ℝ))
      (E := (cell12275 ⟨29, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83074391655257 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (28847865501 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_30 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41519995763531 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (92313329887 / 4000000000000 : ℝ))
      (E := (cell12275 ⟨30, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41519995763531 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (92313329887 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_31 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83005615534669 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307837239609 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨31, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83005615534669 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307837239609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_32 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41485631823161 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230784121973 / 10000000000000 : ℝ))
      (E := (cell12275 ⟨32, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41485631823161 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230784121973 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_33 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41468467915213 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307845189659 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨33, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41468467915213 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307845189659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_34 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20725658013887 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (46156984197 / 2000000000000 : ℝ))
      (E := (cell12275 ⟨34, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20725658013887 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (46156984197 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_35 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (16573670458083 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153926582431 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨35, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (16573670458083 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153926582431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_36 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20708524125979 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153928586639 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨36, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20708524125979 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153928586639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_37 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41399932332547 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307861177747 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨37, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41399932332547 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307861177747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_38 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82765656743153 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307865179251 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨38, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82765656743153 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307865179251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_39 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (82731472707453 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576967294637 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨39, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (82731472707453 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576967294637 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12276_20 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20846268675837 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153824080797 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨20, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20846268675837 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153824080797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_21 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (10418807028069 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230765216593 / 10000000000000 : ℝ))
      (E := (cell12276 ⟨21, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (10418807028069 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230765216593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_22 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (83315862174383 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307656182771 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨22, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (83315862174383 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307656182771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_23 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (10410161564947 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307660158347 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨23, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (10410161564947 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307660158347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_24 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41623373613521 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307664155209 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨24, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41623373613521 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307664155209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_25 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41606113131929 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288458514883 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨25, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41606113131929 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288458514883 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_26 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (3327109183891 / 4000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461534422407 / 20000000000000 : ℝ))
      (E := (cell12276 ⟨26, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (3327109183891 / 4000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461534422407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_27 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (8314325719471 / 10000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153838068853 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨27, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (8314325719471 / 10000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153838068853 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_28 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41554404511873 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461536028201 / 20000000000000 : ℝ))
      (E := (cell12276 ⟨28, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41554404511873 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (461536028201 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_29 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (10384298131517 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307684124977 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨29, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (10384298131517 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307684124977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_30 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20759996311949 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307688092433 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨30, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20759996311949 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307688092433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_31 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41502804789403 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (9014422283 / 390625000000 : ℝ))
      (E := (cell12276 ⟨31, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41502804789403 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (9014422283 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_32 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20742814503353 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307696104921 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨32, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20742814503353 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307696104921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_33 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (4146846526001 / 5000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153850047987 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨33, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (4146846526001 / 5000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153850047987 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_34 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41451313533599 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288463009937 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨34, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41451313533599 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288463009937 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_35 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41434173811837 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576927014287 / 25000000000000 : ℝ))
      (E := (cell12276 ⟨35, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41434173811837 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (576927014287 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_36 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (647141344987 / 781250000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (144232005561 / 6250000000000 : ℝ))
      (E := (cell12276 ⟨36, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (647141344987 / 781250000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (144232005561 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_37 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (8279986064023 / 10000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230771605899 / 10000000000000 : ℝ))
      (E := (cell12276 ⟨37, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (8279986064023 / 10000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230771605899 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_38 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (517285331491 / 625000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288465010677 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨38, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (517285331491 / 625000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288465010677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_39 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (82731469322687 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307724051721 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨39, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (82731469322687 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307724051721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12277_20 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10423133145863 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307503140443 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨20, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10423133145863 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307503140443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_21 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (4167522350801 / 5000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307507156747 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨21, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (4167522350801 / 5000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307507156747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_22 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83315853293303 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307511128057 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨22, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83315853293303 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307511128057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_23 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83281283965491 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307515117139 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨23, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83281283965491 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307515117139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_24 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41623369499747 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153759564143 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨24, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41623369499747 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153759564143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_25 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10401527295299 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576880776801 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨25, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10401527295299 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576880776801 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_26 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16635544404287 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (144220444751 / 6250000000000 : ℝ))
      (E := (cell12277 ⟨26, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16635544404287 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (144220444751 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_27 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83143249944041 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307531099907 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨27, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83143249944041 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307531099907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_28 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16621760419559 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153767531077 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨28, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16621760419559 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153767531077 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_29 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83074378450451 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307539064247 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨29, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83074378450451 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307539064247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_30 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (20759994742481 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307543050599 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨30, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (20759994742481 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307543050599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_31 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41502801812149 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307547082281 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨31, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41502801812149 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307547082281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_32 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10371406547727 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (57688776117 / 2500000000000 : ℝ))
      (E := (cell12277 ⟨32, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10371406547727 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (57688776117 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_33 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10367115651361 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307555056921 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨33, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10367115651361 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307555056921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_34 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (82902622080081 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307559062403 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨34, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (82902622080081 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307559062403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_35 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (132589348733 / 160000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461512612557 / 20000000000000 : ℝ))
      (E := (cell12277 ⟨35, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (132589348733 / 160000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461512612557 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_36 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (20708521953477 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153783529751 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨36, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (20708521953477 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153783529751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_37 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41399928308239 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307571053759 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨37, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41399928308239 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307571053759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_38 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (82765649335039 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307575046539 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨38, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (82765649335039 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307575046539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_39 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (10341433242369 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307579038599 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨39, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (10341433242369 / 12500000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307579038599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12278_20 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10423131954033 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (92294326923 / 4000000000000 : ℝ))
      (E := (cell12278 ⟨20, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10423131954033 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (92294326923 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_21 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (333401751237 / 400000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153681100707 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨21, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (333401751237 / 400000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153681100707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_22 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (16663168882789 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307366185539 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨22, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (16663168882789 / 20000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307366185539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_23 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41640637706543 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288421273527 / 12500000000000 : ℝ))
      (E := (cell12278 ⟨23, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41640637706543 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288421273527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_24 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41623365386793 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230737415541 / 10000000000000 : ℝ))
      (E := (cell12278 ⟨24, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41623365386793 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230737415541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_25 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (20803052615631 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307378149457 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨25, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (20803052615631 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307378149457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_26 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (5198607152947 / 6250000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (72105692943 / 3125000000000 : ℝ))
      (E := (cell12278 ⟨26, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (5198607152947 / 6250000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (72105692943 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_27 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83143242694889 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307386116351 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨27, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83143242694889 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307386116351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_28 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (2077719879333 / 2500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288423769307 / 12500000000000 : ℝ))
      (E := (cell12278 ⟨28, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (2077719879333 / 2500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (288423769307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_29 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (415371859251 / 500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307394116337 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨29, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (415371859251 / 500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307394116337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_30 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83039972693447 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307398121673 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨30, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83039972693447 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307398121673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_31 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83005597671143 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307402114619 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨31, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83005597671143 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307402114619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_32 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41485623375767 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576851524381 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨32, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41485623375767 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576851524381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_33 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (20734229975757 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576852532761 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨33, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (20734229975757 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576852532761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_34 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (20725654273549 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307414100011 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨34, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (20725654273549 / 25000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307414100011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_35 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10358542286721 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576854530797 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨35, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10358542286721 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576854530797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_36 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10354260433829 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153711042429 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨36, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10354260433829 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153711042429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_37 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82799852593837 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (18026766433 / 781250000000 : ℝ))
      (E := (cell12278 ⟨37, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82799852593837 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (18026766433 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_38 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (82765645632589 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153715031311 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨38, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (82765645632589 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153715031311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_39 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10341432819531 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307434080501 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨39, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10341432819531 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307434080501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12279_20 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83385046099427 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307213317727 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨20, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83385046099427 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307213317727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_21 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41675214302121 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576804324983 / 25000000000000 : ℝ))
      (E := (cell12279 ⟨21, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41675214302121 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576804324983 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_22 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83315835536307 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153610648469 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨22, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83315835536307 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153610648469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_23 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83281266862361 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576806328319 / 25000000000000 : ℝ))
      (E := (cell12279 ⟨23, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83281266862361 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576806328319 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_24 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20811680637329 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230722929491 / 10000000000000 : ℝ))
      (E := (cell12279 ⟨24, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20811680637329 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230722929491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_25 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41606101282127 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (144202081511 / 6250000000000 : ℝ))
      (E := (cell12279 ⟨25, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41606101282127 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (144202081511 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_26 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41588853437213 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461447457303 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨26, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41588853437213 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461447457303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_27 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83143235447253 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153620622719 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨27, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83143235447253 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153620622719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_28 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83108788250321 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461449048529 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨28, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83108788250321 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461449048529 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_29 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (16614873050277 / 20000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (72101540039 / 3125000000000 : ℝ))
      (E := (cell12279 ⟨29, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (16614873050277 / 20000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (72101540039 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_30 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20759991604591 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307253247187 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨30, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20759991604591 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307253247187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_31 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83005591719341 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307257259957 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨31, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83005591719341 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307257259957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_32 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20742810280641 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (72101914483 / 3125000000000 : ℝ))
      (E := (cell12279 ⟨32, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20742810280641 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (72101914483 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_33 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (82936914596441 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307265259803 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨33, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (82936914596441 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307265259803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_34 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (10362826513693 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307269250883 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨34, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (10362826513693 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307269250883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_35 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41434166815301 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307273238357 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨35, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41434166815301 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307273238357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_36 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20708519782127 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153638611827 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨36, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20708519782127 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153638611827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_37 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20699962143077 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307281207983 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨37, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20699962143077 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307281207983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_38 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (8276564193121 / 10000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153642596161 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨38, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (8276564193121 / 10000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153642596161 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_39 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (3309258366983 / 4000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230728923611 / 10000000000000 : ℝ))
      (E := (cell12279 ⟨39, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (3309258366983 / 4000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230728923611 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12280_20 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83385036568393 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153534258083 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨20, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83385036568393 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153534258083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_21 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20837604850249 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307072510561 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨21, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20837604850249 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307072510561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_22 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (8331582666039 / 10000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307076520537 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨22, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (8331582666039 / 10000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307076520537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_23 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20820314578329 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (14419253077 / 625000000000 : ℝ))
      (E := (cell12280 ⟨23, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20820314578329 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (14419253077 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_24 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (16649342865337 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115354224423 / 5000000000000 : ℝ))
      (E := (cell12280 ⟨24, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (16649342865337 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115354224423 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_25 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83212194667581 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230708851301 / 10000000000000 : ℝ))
      (E := (cell12280 ⟨25, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83212194667581 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230708851301 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_26 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83177699303257 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230709251141 / 10000000000000 : ℝ))
      (E := (cell12280 ⟨26, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83177699303257 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230709251141 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_27 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20785807050283 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576774121793 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨27, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20785807050283 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576774121793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_28 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20777195332199 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (288387562749 / 12500000000000 : ℝ))
      (E := (cell12280 ⟨28, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20777195332199 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (288387562749 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_29 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20768589663501 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230710444209 / 10000000000000 : ℝ))
      (E := (cell12280 ⟨29, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20768589663501 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230710444209 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_30 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41519980072337 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153554242807 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨30, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41519980072337 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153554242807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_31 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20751396442223 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307112459803 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨31, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20751396442223 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307112459803 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_32 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41485617747453 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153558212723 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨32, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41485617747453 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153558212723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_33 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41468454645563 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1441950277 / 62500000000 : ℝ))
      (E := (cell12280 ⟨33, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41468454645563 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1441950277 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_34 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82902607126123 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153562228229 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨34, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82902607126123 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153562228229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_35 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (20717082242157 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307128408293 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨35, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (20717082242157 / 25000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307128408293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_36 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41417037393767 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461426483457 / 20000000000000 : ℝ))
      (E := (cell12280 ⟨36, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41417037393767 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461426483457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_37 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82799844551889 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (92285457043 / 4000000000000 : ℝ))
      (E := (cell12280 ⟨37, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82799844551889 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (92285457043 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_38 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82765638230901 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576785108911 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨38, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82765638230901 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576785108911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_39 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (82731455793933 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (72098262127 / 3125000000000 : ℝ))
      (E := (cell12280 ⟨39, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (82731455793933 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (72098262127 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12281_20 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83385027039161 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576730956657 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨20, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83385027039161 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576730956657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_21 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83350410199511 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306927833301 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨21, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83350410199511 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306927833301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_22 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41657908893097 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461386359611 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨22, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41657908893097 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461386359611 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_23 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83281249765949 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461387156731 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨23, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83281249765949 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461387156731 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_24 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20811676526423 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (230693979439 / 10000000000000 : ℝ))
      (E := (cell12281 ⟨24, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20811676526423 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (230693979439 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_25 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41606093386253 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (57673594399 / 2500000000000 : ℝ))
      (E := (cell12281 ⟨25, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41606093386253 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (57673594399 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_26 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20794422933411 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306947790487 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨26, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20794422933411 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306947790487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_27 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83143220956527 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306951783153 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨27, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83143220956527 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306951783153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_28 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41554387204373 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306955757229 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨28, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41554387204373 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306955757229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_29 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (10384294007257 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306959774203 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨29, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (10384294007257 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306959774203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_30 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41519976936189 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461392755697 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨30, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41519976936189 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461392755697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_31 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83005579819797 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306967772649 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨31, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83005579819797 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306967772649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_32 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82971229868561 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153485879521 / 50000000000000 : ℝ))
      (E := (cell12281 ⟨32, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82971229868561 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153485879521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_33 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82936903987083 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (92279029591 / 4000000000000 : ℝ))
      (E := (cell12281 ⟨33, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82936903987083 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (92279029591 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_34 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82902602143933 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153489858369 / 50000000000000 : ℝ))
      (E := (cell12281 ⟨34, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82902602143933 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153489858369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_35 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16573664861569 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306983750173 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨35, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16573664861569 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306983750173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_36 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82834070447711 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (57674693109 / 2500000000000 : ℝ))
      (E := (cell12281 ⟨36, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82834070447711 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (57674693109 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_37 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82799840532581 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153495849533 / 50000000000000 : ℝ))
      (E := (cell12281 ⟨37, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82799840532581 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153495849533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_38 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82765634531663 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288374466741 / 12500000000000 : ℝ))
      (E := (cell12281 ⟨38, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82765634531663 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (288374466741 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_39 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (82731452414321 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306999712409 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨39, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (82731452414321 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306999712409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12282_20 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83385017511731 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306779190879 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨20, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83385017511731 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306779190879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_21 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83350400999787 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306783151639 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨21, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83350400999787 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306783151639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_22 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (20828952228429 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306787187777 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨22, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (20828952228429 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306787187777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_23 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83281241220261 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153395593641 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨23, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83281241220261 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153395593641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_24 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83246697886337 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306795154371 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨24, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83246697886337 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306795154371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_25 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83212178879027 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306799151381 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨25, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83212178879027 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306799151381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_26 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41588842082793 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576700780937 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨26, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41588842082793 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576700780937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_27 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83143213713437 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153403566691 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨27, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83143213713437 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153403566691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_28 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (8310876749017 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153405562601 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨28, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (8310876749017 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153405562601 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_29 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41537172731771 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306815102249 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨29, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41537172731771 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306815102249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_30 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41519973800737 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (11534095629 / 500000000000 : ℝ))
      (E := (cell12282 ⟨30, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41519973800737 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (11534095629 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_31 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83005573872053 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153411570003 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨31, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83005573872053 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153411570003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_32 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (10371403030441 / 12500000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461365417739 / 20000000000000 : ℝ))
      (E := (cell12282 ⟨32, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (10371403030441 / 12500000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461365417739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_33 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (8293689868431 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (144176943187 / 6250000000000 : ℝ))
      (E := (cell12282 ⟨33, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (8293689868431 / 10000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (144176943187 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_34 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41451298581487 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153417545143 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨34, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41451298581487 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153417545143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_35 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82868319648253 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461367817647 / 20000000000000 : ℝ))
      (E := (cell12282 ⟨35, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82868319648253 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (461367817647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_36 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41417033054519 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306843086269 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨36, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41417033054519 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306843086269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_37 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82799836514383 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230684708559 / 10000000000000 : ℝ))
      (E := (cell12282 ⟨37, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82799836514383 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230684708559 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_38 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (16553126166699 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306851087177 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨38, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (16553126166699 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306851087177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_39 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (82731449035739 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306855091783 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨39, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (82731449035739 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306855091783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12283_20 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83385007986103 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153317304461 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨20, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83385007986103 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153317304461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_21 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83350391801823 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306638640351 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨21, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83350391801823 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306638640351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_22 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41657900021479 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153321315711 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨22, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41657900021479 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153321315711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_23 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83281232676251 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (72082705831 / 3125000000000 : ℝ))
      (E := (cell12283 ⟨23, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83281232676251 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (72082705831 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_24 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41623344834309 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306650626737 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨24, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41623344834309 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306650626737 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_25 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (10401521373393 / 12500000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153327290461 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨25, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (10401521373393 / 12500000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153327290461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_26 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (20794419149771 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306658569571 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨26, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (20794419149771 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306658569571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_27 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41571603235931 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306662596261 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨27, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41571603235931 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306662596261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_28 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (20777190143267 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461333321183 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨28, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (20777190143267 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461333321183 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_29 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83074338870461 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (230667060157 / 10000000000000 : ℝ))
      (E := (cell12283 ⟨29, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83074338870461 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (230667060157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_30 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83039941331963 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (144167161627 / 6250000000000 : ℝ))
      (E := (cell12283 ⟨30, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83039941331963 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (144167161627 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_31 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83005567925661 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576669640469 / 25000000000000 : ℝ))
      (E := (cell12283 ⟨31, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83005567925661 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576669640469 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_32 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41485609309903 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (57667064749 / 2500000000000 : ℝ))
      (E := (cell12283 ⟨32, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41485609309903 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (57667064749 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_33 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (82936893382809 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306686555391 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨33, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (82936893382809 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306686555391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_34 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41451296091623 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461338115421 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨34, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41451296091623 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461338115421 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_35 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (1657366299797 / 2000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153347269829 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨35, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (1657366299797 / 2000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153347269829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_36 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (20708515442879 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306698561627 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨36, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (20708515442879 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306698561627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_37 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41399916248647 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153351263509 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨37, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41399916248647 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153351263509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_38 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (20691406784099 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576676638513 / 25000000000000 : ℝ))
      (E := (cell12283 ⟨38, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (20691406784099 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576676638513 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_39 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41365722829093 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (230671052619 / 10000000000000 : ℝ))
      (E := (cell12283 ⟨39, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41365722829093 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (230671052619 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12284_20 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (3335399938491 / 4000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306490138993 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨20, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (3335399938491 / 4000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306490138993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_21 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83350382605619 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306494182921 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨21, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83350382605619 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306494182921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_22 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41657895586959 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306498128991 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨22, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41657895586959 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306498128991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_23 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83281224133919 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306502156503 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨23, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83281224133919 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306502156503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_24 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (10405835181567 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306506153159 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨24, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (10405835181567 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306506153159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_25 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83212163096857 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288313765367 / 12500000000000 : ℝ))
      (E := (cell12284 ⟨25, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83212163096857 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288313765367 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_26 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (10397208629267 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576628531989 / 25000000000000 : ℝ))
      (E := (cell12284 ⟨26, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (10397208629267 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576628531989 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_27 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (415715996159 / 500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153259056697 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨27, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (415715996159 / 500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153259056697 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_28 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83108753657439 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153261070473 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨28, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83108753657439 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153261070473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_29 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83074332278813 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306526096827 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨29, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83074332278813 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306526096827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_30 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20759983765961 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288316262589 / 12500000000000 : ℝ))
      (E := (cell12284 ⟨30, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20759983765961 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288316262589 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_31 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83005561980621 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306534096751 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨31, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83005561980621 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306534096751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_32 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41485606498697 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288317260911 / 12500000000000 : ℝ))
      (E := (cell12284 ⟨32, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41485606498697 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (288317260911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_33 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82936888082579 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (36039719913 / 1562500000000 : ℝ))
      (E := (cell12284 ⟨33, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82936888082579 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (36039719913 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_34 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20725646801187 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306546060069 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨34, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20725646801187 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306546060069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_35 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41434155166319 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306550104441 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨35, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41434155166319 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306550104441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_36 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82834057435143 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306554091823 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨36, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82834057435143 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306554091823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_37 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20699957120329 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153279040991 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨37, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20699957120329 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153279040991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_38 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82765623440367 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153281037947 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨38, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82765623440367 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153281037947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_39 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (82731442281663 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (230656607431 / 10000000000000 : ℝ))
      (E := (cell12284 ⟨39, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (82731442281663 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (230656607431 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12285_20 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (10423123617531 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576586445273 / 25000000000000 : ℝ))
      (E := (cell12285 ⟨20, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (10423123617531 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576586445273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_21 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41675186705587 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306349779351 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨21, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41675186705587 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306349779351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_22 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83315782306597 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306353738767 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨22, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83315782306597 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306353738767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_23 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (5205075974579 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461271556081 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨23, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (5205075974579 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461271556081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_24 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (8324667323809 / 10000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576590433409 / 25000000000000 : ℝ))
      (E := (cell12285 ⟨24, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (8324667323809 / 10000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576590433409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_25 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (16642431041633 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306365719073 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨25, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (16642431041633 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306365719073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_26 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83177661470743 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (144148108783 / 6250000000000 : ℝ))
      (E := (cell12285 ⟨26, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83177661470743 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (144148108783 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_27 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (20785797998313 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153186871589 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨27, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (20785797998313 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153186871589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_28 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83108746743283 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461275546059 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨28, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83108746743283 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461275546059 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_29 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83074325688597 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153190852457 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨29, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83074325688597 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153190852457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_30 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83039928797117 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230638572831 / 10000000000000 : ℝ))
      (E := (cell12285 ⟨30, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83039928797117 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230638572831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_31 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (20751389009233 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306389686141 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨31, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (20751389009233 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306389686141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_32 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41485603688147 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230639369771 / 10000000000000 : ℝ))
      (E := (cell12285 ⟨32, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41485603688147 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230639369771 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_33 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41468441391809 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306397706659 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨33, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41468441391809 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306397706659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_34 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (2072564555687 / 2500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230640171487 / 10000000000000 : ℝ))
      (E := (cell12285 ⟨34, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (2072564555687 / 2500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230640171487 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_35 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (16573661135323 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230640566541 / 10000000000000 : ℝ))
      (E := (cell12285 ⟨35, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (16573661135323 / 20000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (230640566541 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_36 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82834053099919 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153204838429 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨36, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82834053099919 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153204838429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_37 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41399912233223 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (46128273837 / 2000000000000 : ℝ))
      (E := (cell12285 ⟨37, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41399912233223 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (46128273837 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_38 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41382809872703 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (72075551647 / 3125000000000 : ℝ))
      (E := (cell12285 ⟨38, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41382809872703 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (72075551647 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_39 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (82731438906169 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153210838731 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨39, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (82731438906169 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153210838731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12286_20 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83384979420021 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576550369247 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨20, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83384979420021 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576550369247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_21 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83350364218487 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461241085929 / 20000000000000 : ℝ))
      (E := (cell12286 ⟨21, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83350364218487 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461241085929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_22 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83315773440993 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153104730377 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨22, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83315773440993 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153104730377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_23 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (16656241410857 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153106729151 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨23, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (16656241410857 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153106729151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_24 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (65036457051 / 78125000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306217426503 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨24, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (65036457051 / 78125000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306217426503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_25 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20803036830267 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306221427687 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨25, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20803036830267 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306221427687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_26 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10397206738613 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576556351823 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨26, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10397206738613 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576556351823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_27 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83143184756217 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306229427219 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨27, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83143184756217 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306229427219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_28 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (415543699153 / 500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576558358097 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨28, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (415543699153 / 500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576558358097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_29 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83074319099813 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153118712917 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨29, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83074319099813 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153118712917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_30 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83039922531781 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306241410361 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨30, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83039922531781 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306241410361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_31 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83005550094593 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153122694271 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨31, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83005550094593 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153122694271 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_32 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10371400219563 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461249872543 / 20000000000000 : ℝ))
      (E := (cell12286 ⟨32, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10371400219563 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (461249872543 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_33 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10367109685741 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306253393533 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨33, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10367109685741 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306253393533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_34 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82902577251441 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115312868291 / 5000000000000 : ℝ))
      (E := (cell12286 ⟨34, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82902577251441 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115312868291 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_35 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82868301021781 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306261398333 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨35, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82868301021781 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306261398333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_36 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20708512191461 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306265375347 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨36, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20708512191461 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306265375347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_37 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (16559964090537 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (18450154853 / 800000000000 : ℝ))
      (E := (cell12286 ⟨37, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (16559964090537 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (18450154853 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_38 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (16553123210303 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288284167893 / 12500000000000 : ℝ))
      (E := (cell12286 ⟨38, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (16553123210303 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288284167893 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_39 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (82731435531703 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576569333913 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨39, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (82731435531703 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576569333913 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12287_20 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83384969901593 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153028613341 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨20, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83384969901593 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153028613341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_21 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83350355027559 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153030596029 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨21, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83350355027559 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153030596029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_22 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83315764577107 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306065236669 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨22, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83315764577107 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306065236669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_23 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83281198516983 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306069190191 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨23, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83281198516983 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306069190191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_24 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41623328407053 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576518293357 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨24, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41623328407053 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576518293357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_25 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16642427887113 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153038595213 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨25, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16642427887113 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153038595213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_26 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83177646348619 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306081186621 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨26, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83177646348619 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306081186621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_27 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (10392897190087 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153042582757 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨27, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (10392897190087 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153042582757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_28 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83108732919389 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153044594401 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨28, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83108732919389 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153044594401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_29 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (4153715625623 / 5000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (115304660057 / 5000000000000 : ℝ))
      (E := (cell12287 ⟨29, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (4153715625623 / 5000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (115304660057 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_30 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16607983253567 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (144131071679 / 6250000000000 : ℝ))
      (E := (cell12287 ⟨30, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16607983253567 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (144131071679 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_31 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16601108830721 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306101145459 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨31, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16601108830721 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306101145459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_32 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (10371399517253 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153052570409 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨32, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (10371399517253 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153052570409 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_33 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82936872189507 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306109135053 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨33, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82936872189507 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306109135053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_34 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (10362821534579 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576528282511 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨34, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (10362821534579 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576528282511 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_35 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (82868296368137 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306117127443 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨35, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (82868296368137 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306117127443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_36 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41417022216459 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576530282169 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨36, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41417022216459 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576530282169 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_37 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (2587494263751 / 3125000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306125134941 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨37, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (2587494263751 / 3125000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306125134941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_38 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20691403089673 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576532286803 / 25000000000000 : ℝ))
      (E := (cell12287 ⟨38, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20691403089673 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (576532286803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_39 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16546286431653 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306133107559 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨39, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16546286431653 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306133107559 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12288_20 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (20846240096241 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305913088409 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨20, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (20846240096241 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305913088409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_21 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83350345838389 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576479266649 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨21, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83350345838389 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576479266649 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_22 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41657877857469 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152960533257 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨22, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41657877857469 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152960533257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_23 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83281189981357 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152962517191 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨23, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83281189981357 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152962517191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_24 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41623324302283 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (288241129093 / 12500000000000 : ℝ))
      (E := (cell12288 ⟨24, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41623324302283 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (288241129093 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_25 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (10401516443957 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152966532823 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨25, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (10401516443957 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152966532823 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_26 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83177638789887 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305937020143 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨26, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83177638789887 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305937020143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_27 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41571585143343 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305941016469 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨27, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41571585143343 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305941016469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_28 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83108726009649 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115297249977 / 5000000000000 : ℝ))
      (E := (cell12288 ⟨28, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83108726009649 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115297249977 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_29 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83074305926539 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461189806167 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨29, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83074305926539 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461189806167 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_30 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83039910005281 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305952996289 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨30, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83039910005281 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305952996289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_31 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83005538213967 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576489253847 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨31, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83005538213967 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576489253847 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_32 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82971190520853 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152980486753 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨32, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82971190520853 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152980486753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_33 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (16587373378871 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576491247441 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨33, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (16587373378871 / 20000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576491247441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_34 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82902567303051 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305969007547 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨34, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82902567303051 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305969007547 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_35 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82868291715681 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (7206165531 / 312500000000 : ℝ))
      (E := (cell12288 ⟨35, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82868291715681 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (7206165531 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_36 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82834040101141 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115298849773 / 5000000000000 : ℝ))
      (E := (cell12288 ⟨36, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82834040101141 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (115298849773 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_37 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (10349976553561 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461196193633 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨37, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (10349976553561 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461196193633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_38 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (82765608666937 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576496236899 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨38, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (82765608666937 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576496236899 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_39 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (1292678574779 / 1562500000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461197798637 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨39, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (1292678574779 / 1562500000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461197798637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12289_20 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41692475435067 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152884501969 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨20, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41692475435067 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152884501969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_21 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83350336650977 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305772994999 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨21, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83350336650977 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305772994999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_22 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16663149370897 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152888504287 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨22, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16663149370897 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152888504287 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_23 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41640590723703 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152890495439 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨23, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41640590723703 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152890495439 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_24 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83246640396661 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576446236531 / 25000000000000 : ℝ))
      (E := (cell12289 ⟨24, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83246640396661 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576446236531 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_25 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83212123669341 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152894497497 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨25, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83212123669341 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152894497497 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_26 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (20794407808177 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (461158593247 / 20000000000000 : ℝ))
      (E := (cell12289 ⟨26, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (20794407808177 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (461158593247 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_27 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83143163054189 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152898490041 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨27, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83143163054189 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152898490041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_28 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83108719101381 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92232036921 / 4000000000000 : ℝ))
      (E := (cell12289 ⟨28, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83108719101381 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92232036921 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_29 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (2596071854439 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305804914921 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨29, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (2596071854439 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305804914921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_30 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (20759975936029 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152904479321 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨30, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (20759975936029 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152904479321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_31 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83005532275679 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305812939839 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨31, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83005532275679 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305812939839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_32 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (2592849528281 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305816919297 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨32, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (2592849528281 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305816919297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_33 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (10367107700059 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (18446567193 / 800000000000 : ℝ))
      (E := (cell12289 ⟨33, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (10367107700059 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (18446567193 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_34 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82902562330699 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152912469883 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨34, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82902562330699 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152912469883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_35 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82868287064413 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152914462883 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨35, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82868287064413 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152914462883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_36 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82834035770511 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230583291709 / 10000000000000 : ℝ))
      (E := (cell12289 ⟨36, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82834035770511 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (230583291709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_37 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (20699952104513 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152918457467 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨37, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (20699952104513 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152918457467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_38 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (82765604976249 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305840920273 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨38, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (82765604976249 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305840920273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_39 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (3309257016579 / 4000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305844875169 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨39, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (3309257016579 / 4000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305844875169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12290_20 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41692470678551 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576406243317 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨20, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41692470678551 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576406243317 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_21 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83350327465321 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288203622159 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨21, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83350327465321 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288203622159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_22 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83315737995747 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288204125571 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨22, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83315737995747 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288204125571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_23 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (8328117291513 / 10000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305637001373 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨23, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (8328117291513 / 10000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305637001373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_24 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (8324663219039 / 10000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152820485949 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨24, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (8324663219039 / 10000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152820485949 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_25 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83212115788619 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288205622309 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨25, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83212115788619 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288205622309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_26 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83177623677081 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576412241631 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨26, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83177623677081 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576412241631 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_27 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83143155823203 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305652939557 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨27, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83143155823203 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305652939557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_28 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (10388589024323 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305656959261 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨28, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (10388589024323 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305656959261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_29 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83074292758987 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576415242573 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨29, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83074292758987 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576415242573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_30 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83039897484341 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305664916981 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨30, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83039897484341 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305664916981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_31 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (4150276316937 / 5000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305668918811 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨31, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (4150276316937 / 5000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305668918811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_32 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82971179290439 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (92226916787 / 4000000000000 : ℝ))
      (E := (cell12290 ⟨32, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82971179290439 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (92226916787 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_33 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82936856307857 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305676921679 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨33, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82936856307857 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305676921679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_34 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (3316102294383 / 4000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152840463351 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨34, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (3316102294383 / 4000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152840463351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_35 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (20717070603583 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461136987279 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨35, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (20717070603583 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461136987279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_36 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82834031441029 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152844446783 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨36, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82834031441029 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152844446783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_37 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82799804408723 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461138583323 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨37, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82799804408723 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461138583323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_38 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (82765601286629 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152848444633 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨38, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (82765601286629 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152848444633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_39 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (2068285551103 / 2500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576425217719 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨39, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (2068285551103 / 2500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576425217719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12291_20 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83384931845867 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152740527319 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨20, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83384931845867 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152740527319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_21 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41675159140711 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288185633959 / 12500000000000 : ℝ))
      (E := (cell12291 ⟨21, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41675159140711 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288185633959 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_22 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41657864569363 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305489054497 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨22, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41657864569363 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305489054497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_23 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (5205072774033 / 6250000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305493065869 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨23, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (5205072774033 / 6250000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305493065869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_24 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (10405827998219 / 12500000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305497051739 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨24, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (10405827998219 / 12500000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305497051739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_25 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (8321210790949 / 10000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576375268609 / 25000000000000 : ℝ))
      (E := (cell12291 ⟨25, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (8321210790949 / 10000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576375268609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_26 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41588808061503 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (230550502101 / 10000000000000 : ℝ))
      (E := (cell12291 ⟨26, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41588808061503 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (230550502101 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_27 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83143148593729 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152754505847 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨27, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83143148593729 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152754505847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_28 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83108705289257 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (92220521993 / 4000000000000 : ℝ))
      (E := (cell12291 ⟨28, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83108705289257 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (92220521993 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_29 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83074286177357 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305517021609 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨29, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83074286177357 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305517021609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_30 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (20759972806489 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152760523359 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨30, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (20759972806489 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152760523359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_31 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (1660110408063 / 2000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (5763812527 / 250000000000 : ℝ))
      (E := (cell12291 ⟨31, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (1660110408063 / 2000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (5763812527 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_32 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (16594234735439 / 20000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152764516579 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨32, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (16594234735439 / 20000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152764516579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_33 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82936851016511 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305532998887 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨33, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82936851016511 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305532998887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_34 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82902552389679 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305537026921 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨34, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82902552389679 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305537026921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_35 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (258963368017 / 312500000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461108200361 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨35, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (258963368017 / 312500000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461108200361 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_36 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41417013556347 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305544983503 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨36, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41417013556347 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305544983503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_37 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82799800400501 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305548973209 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨37, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82799800400501 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305548973209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_38 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82765597598077 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461110594379 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨38, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82765597598077 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461110594379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_39 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (82731418674793 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305556980307 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨39, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (82731418674793 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305556980307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12292_20 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (8338492233643 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144083578003 / 6250000000000 : ℝ))
      (E := (cell12292 ⟨20, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (8338492233643 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144083578003 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_21 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83350309099279 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (288167652493 / 12500000000000 : ℝ))
      (E := (cell12292 ⟨21, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83350309099279 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (288167652493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_22 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83315720283419 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461069043329 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨22, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83315720283419 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461069043329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_23 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83281155855601 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144084327667 / 6250000000000 : ℝ))
      (E := (cell12292 ⟨23, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83281155855601 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144084327667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_24 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83246615782747 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305353243977 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨24, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83246615782747 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305353243977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_25 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83212100031953 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576339306133 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨25, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83212100031953 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576339306133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_26 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41588804285241 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305361188071 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨26, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41588804285241 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305361188071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_27 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (16628628273153 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461073039299 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨27, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (16628628273153 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461073039299 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_28 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83108698385401 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305369194717 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨28, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83108698385401 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305369194717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_29 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20768569899289 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305373185767 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨29, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20768569899289 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305373185767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_30 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (16218727533 / 19531250000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576344293111 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨30, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (16218727533 / 19531250000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576344293111 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_31 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20751378617227 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461076231463 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨31, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20751378617227 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461076231463 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_32 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41485584032629 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305385201233 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨32, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41485584032629 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305385201233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_33 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (2591776428951 / 3125000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (230538918929 / 10000000000000 : ℝ))
      (E := (cell12292 ⟨33, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (2591776428951 / 3125000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (230538918929 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_34 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (8290254742101 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305393181859 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨34, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (8290254742101 / 10000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305393181859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_35 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41434136558867 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305397180589 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨35, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41434136558867 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305397180589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_36 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82834022785507 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305401128287 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨36, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82834022785507 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305401128287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_37 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82799796393387 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305405143351 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨37, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82799796393387 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305405143351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_38 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82765593910591 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305409168161 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨38, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82765593910591 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305409168161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_39 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (82731415306493 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305413144781 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨39, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (82731415306493 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305413144781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12293_20 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83384912828789 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461038699053 / 20000000000000 : ℝ))
      (E := (cell12293 ⟨20, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83384912828789 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461038699053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_21 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (20837574979723 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461039496069 / 20000000000000 : ℝ))
      (E := (cell12293 ⟨21, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (20837574979723 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461039496069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_22 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83315711429827 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576300372753 / 25000000000000 : ℝ))
      (E := (cell12293 ⟨22, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83315711429827 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576300372753 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_23 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83281147328347 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152602736739 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨23, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83281147328347 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152602736739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_24 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (1300728243459 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305209431953 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨24, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (1300728243459 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305209431953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_25 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83212092156009 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305213428761 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨25, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83212092156009 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305213428761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_26 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (8317760101951 / 10000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305217467707 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨26, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (8317760101951 / 10000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305217467707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_27 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83143134139311 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305221435561 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨27, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83143134139311 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305221435561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_28 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41554345741507 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305225452363 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨28, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41554345741507 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305225452363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_29 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (5192142063649 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (14407683777 / 625000000000 : ℝ))
      (E := (cell12293 ⟨29, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (5192142063649 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (14407683777 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_30 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (10379984839169 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305233411101 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨30, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (10379984839169 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305233411101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_31 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41502754268007 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305237416849 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨31, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41502754268007 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305237416849 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_32 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (8297116245463 / 10000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288155177987 / 12500000000000 : ℝ))
      (E := (cell12293 ⟨32, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (8297116245463 / 10000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288155177987 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_33 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (4146842021881 / 5000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305245434349 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨33, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (4146842021881 / 5000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305245434349 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_34 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (1295352225837 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152624695759 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨34, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (1295352225837 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152624695759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_35 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (5179266779451 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305253414157 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨35, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (5179266779451 / 6250000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305253414157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_36 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41417009229733 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152628693267 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨36, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41417009229733 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152628693267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_37 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41399896193689 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305261368409 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨37, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41399896193689 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305261368409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_38 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82765590224171 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305265360749 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨38, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82765590224171 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305265360749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_39 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (82731411939219 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305269364299 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨39, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (82731411939219 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305269364299 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12294_20 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (16676980664589 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230504979629 / 10000000000000 : ℝ))
      (E := (cell12294 ⟨20, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (16676980664589 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230504979629 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_21 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (4167514537013 / 5000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152526897311 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨21, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (4167514537013 / 5000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152526897311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_22 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83315702577949 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152528880519 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨22, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83315702577949 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152528880519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_23 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41640569401383 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305061758291 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨23, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41640569401383 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305061758291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_24 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20811649845409 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305065790661 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨24, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20811649845409 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305065790661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_25 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (16642416856331 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152534872741 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨25, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (16642416856331 / 20000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152534872741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_26 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (10397199183761 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230507374317 / 10000000000000 : ℝ))
      (E := (cell12294 ⟨26, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (10397199183761 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230507374317 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_27 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (1299111358037 / 1562500000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461015545779 / 20000000000000 : ℝ))
      (E := (cell12294 ⟨27, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (1299111358037 / 1562500000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461015545779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_28 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83108684582097 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152540882171 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨28, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83108684582097 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152540882171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_29 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (1038428330513 / 1250000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (57627143393 / 2500000000000 : ℝ))
      (E := (cell12294 ⟨29, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (1038428330513 / 1250000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (57627143393 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_30 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20759968114783 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152544881347 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨30, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20759968114783 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152544881347 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_31 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20751375651117 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305093730911 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨31, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20751375651117 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305093730911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_32 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82971156845309 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305097701153 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨32, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82971156845309 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305097701153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_33 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20734208787519 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152550867033 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨33, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20734208787519 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152550867033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_34 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82902537487353 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (72034553577 / 3125000000000 : ℝ))
      (E := (cell12294 ⟨34, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82902537487353 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (72034553577 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_35 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20717065956471 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152554851257 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨35, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20717065956471 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152554851257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_36 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (82834014134571 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152556849817 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨36, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (82834014134571 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152556849817 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_37 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20699947095619 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305117707019 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨37, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20699947095619 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305117707019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_38 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41382793269409 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576280431409 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨38, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41382793269409 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576280431409 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_39 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (20682852143243 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152562848773 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨39, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (20682852143243 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152562848773 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12295_20 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (5211555863681 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304906209361 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨20, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (5211555863681 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304906209361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_21 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41675140781691 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152455081387 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨21, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41675140781691 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152455081387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_22 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16663138745557 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304914201569 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨22, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16663138745557 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304914201569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_23 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41640565139429 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288114769427 / 12500000000000 : ℝ))
      (E := (cell12295 ⟨23, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41640565139429 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288114769427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_24 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (10405823897941 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (230492214511 / 10000000000000 : ℝ))
      (E := (cell12295 ⟨24, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (10405823897941 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (230492214511 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_25 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83212076408893 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304926174691 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨25, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83212076408893 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304926174691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_26 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (10397198240277 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576232532803 / 25000000000000 : ℝ))
      (E := (cell12295 ⟨26, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (10397198240277 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576232532803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_27 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41571559845467 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (144058383431 / 6250000000000 : ℝ))
      (E := (cell12295 ⟨27, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41571559845467 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (144058383431 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_28 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (10388584710331 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460987626131 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨28, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (10388584710331 / 12500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460987626131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_29 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41537129932563 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576235530379 / 25000000000000 : ℝ))
      (E := (cell12295 ⟨29, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41537129932563 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576235530379 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_30 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (830398662063 / 1000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152473055139 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨30, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (830398662063 / 1000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152473055139 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_31 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (8300549667427 / 10000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304950099501 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨31, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (8300549667427 / 10000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304950099501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_32 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16594230247459 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304954091521 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨32, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16594230247459 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304954091521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_33 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41468414931899 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304958088441 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨33, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41468414931899 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304958088441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_34 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (20725633130591 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152481046067 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨34, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (20725633130591 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152481046067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_35 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41434129590869 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304966104247 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨35, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41434129590869 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304966104247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_36 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41417004905411 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304970126199 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨36, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41417004905411 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304970126199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_37 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (2069994609467 / 2500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152487050273 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨37, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (2069994609467 / 2500000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152487050273 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_38 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (82765582854531 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460995617369 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨38, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (82765582854531 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460995617369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_39 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (330925620831 / 400000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (28812276073 / 1250000000000 : ℝ))
      (E := (cell12295 ⟨39, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (330925620831 / 400000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (28812276073 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12296_20 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83384884316643 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576190669061 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨20, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83384884316643 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576190669061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_21 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83350272388259 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304766643063 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨21, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83350272388259 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304766643063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_22 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83315684879333 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304770637763 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨22, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83315684879333 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304770637763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_23 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41640560878311 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304774664857 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨23, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41640560878311 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304774664857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_24 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (20811645746763 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576194652991 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨24, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (20811645746763 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576194652991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_25 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83212068537721 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304782599689 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨25, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83212068537721 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304782599689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_26 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (16635515675179 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460957326367 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨26, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (16635515675179 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460957326367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_27 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (8314311246901 / 10000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304790595167 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨27, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (8314311246901 / 10000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304790595167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_28 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (20777167696167 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304794609727 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨28, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (20777167696167 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304794609727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_29 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83074253290639 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152399310081 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨29, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83074253290639 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152399310081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_30 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (10379982494357 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230480262927 / 10000000000000 : ℝ))
      (E := (cell12296 ⟨30, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (10379982494357 / 12500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230480262927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_31 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41502745372709 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152403290559 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨31, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41502745372709 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152403290559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_32 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82971145630587 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576202648751 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨32, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82971145630587 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576202648751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_33 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82936824578787 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (14405091341 / 625000000000 : ℝ))
      (E := (cell12296 ⟨33, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82936824578787 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (14405091341 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_34 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41451263779301 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152409291547 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨34, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41451263779301 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152409291547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_35 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41434127269389 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304822560771 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨35, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41434127269389 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304822560771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_36 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82834005488219 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304826549007 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨36, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82834005488219 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304826549007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_37 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82799780375989 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460966109799 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨37, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82799780375989 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460966109799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_38 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (82765579171309 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (23048345617 / 1000000000000 : ℝ))
      (E := (cell12296 ⟨38, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (82765579171309 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (23048345617 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_39 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41365700921777 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152419293933 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨39, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41365700921777 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152419293933 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12297_20 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (10423109352023 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152309598469 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨20, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (10423109352023 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152309598469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_21 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83350263214889 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (230462317723 / 10000000000000 : ℝ))
      (E := (cell12297 ⟨21, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83350263214889 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (230462317723 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_22 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (16663135206519 / 20000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (115231359309 / 5000000000000 : ℝ))
      (E := (cell12297 ⟨22, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (16663135206519 / 20000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (115231359309 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_23 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41640556618029 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304631169999 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨23, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41640556618029 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304631169999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_24 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83246574792207 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304635191221 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨24, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83246574792207 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304635191221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_25 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83212060668139 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576159798883 / 25000000000000 : ℝ))
      (E := (cell12297 ⟨25, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83212060668139 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576159798883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_26 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41588785415561 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288080398333 / 12500000000000 : ℝ))
      (E := (cell12297 ⟨26, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41588785415561 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288080398333 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_27 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41571552624297 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (230464716811 / 10000000000000 : ℝ))
      (E := (cell12297 ⟨27, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41571552624297 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (230464716811 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_28 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20777165972039 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152325571567 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨28, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20777165972039 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152325571567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_29 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83074246717579 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304655173209 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨29, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83074246717579 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304655173209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_30 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83039853704799 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (36010299129 / 1562500000000 : ℝ))
      (E := (cell12297 ⟨30, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83039853704799 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (36010299129 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_31 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83005484817913 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460932623453 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨31, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83005484817913 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460932623453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_32 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41485570012593 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152333576541 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨32, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41485570012593 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152333576541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_33 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82936819295041 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304671136799 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨33, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82936819295041 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304671136799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_34 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (2590703831127 / 3125000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152337564391 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨34, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (2590703831127 / 3125000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152337564391 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_35 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82868249897003 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152339565337 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨35, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82868249897003 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152339565337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_36 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82834001166761 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460936628779 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨36, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82834001166761 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460936628779 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_37 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20699944093601 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152343555499 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨37, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20699944093601 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152343555499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_38 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (646606058509 / 781250000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304691091539 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨38, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (646606058509 / 781250000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304691091539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_39 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (82731398480383 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304695086259 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨39, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (82731398480383 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304695086259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12298_20 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (1042310816469 / 1250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576118957421 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨20, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (1042310816469 / 1250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576118957421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_21 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83350254043273 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (144029988971 / 6250000000000 : ℝ))
      (E := (cell12298 ⟨21, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83350254043273 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (144029988971 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_22 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83315667187569 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576120961707 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨22, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83315667187569 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576120961707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_23 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41640552358583 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (115224389373 / 5000000000000 : ℝ))
      (E := (cell12298 ⟨23, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41640552358583 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (115224389373 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_24 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (5202910412437 / 6250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304491824557 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨24, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (5202910412437 / 6250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304491824557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_25 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83212052800147 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460899157433 / 20000000000000 : ℝ))
      (E := (cell12298 ⟨25, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83212052800147 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460899157433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_26 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83177563287899 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304499795701 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨26, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83177563287899 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304499795701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_27 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41571549014843 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304503795327 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨27, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41571549014843 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304503795327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_28 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (10388582124139 / 12500000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (288063473663 / 12500000000000 : ℝ))
      (E := (cell12298 ⟨28, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (10388582124139 / 12500000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (288063473663 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_29 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83074240145947 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152255890329 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨29, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83074240145947 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152255890329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_30 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (648748808251 / 781250000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304515772183 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨30, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (648748808251 / 781250000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304515772183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_31 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (16601095778351 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304519766439 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨31, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (16601095778351 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304519766439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_32 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (8297113442109 / 10000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (225051149 / 9765625000 : ℝ))
      (E := (cell12298 ⟨32, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (8297113442109 / 10000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (225051149 / 9765625000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_33 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82936814012561 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304527772243 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨33, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82936814012561 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304527772243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_34 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82902517634753 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576132932299 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨34, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82902517634753 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576132932299 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_35 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82868245256413 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230453575537 / 10000000000000 : ℝ))
      (E := (cell12298 ⟨35, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82868245256413 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230453575537 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_36 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82833996846449 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304539735027 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨36, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82833996846449 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304539735027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_37 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (20699943093481 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576135931981 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨37, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (20699943093481 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576135931981 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_38 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (4138278590403 / 5000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (92181909401 / 4000000000000 : ℝ))
      (E := (cell12298 ⟨38, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (4138278590403 / 5000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (92181909401 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_39 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (82731395118237 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304551757069 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨39, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (82731395118237 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304551757069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12299_20 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (1667697116413 / 2000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576083129061 / 25000000000000 : ℝ))
      (E := (cell12299 ⟨20, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (1667697116413 / 2000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576083129061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_21 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8335024487341 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576084130931 / 25000000000000 : ℝ))
      (E := (cell12299 ⟨21, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8335024487341 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576084130931 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_22 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (16663131668851 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304340503139 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨22, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (16663131668851 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304340503139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_23 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (10410137024993 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (57608612931 / 2500000000000 : ℝ))
      (E := (cell12299 ⟨23, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (10410137024993 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (57608612931 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_24 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83246558407407 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304348511969 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨24, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83246558407407 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304348511969 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_25 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (5200752808359 / 6250000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460870498259 / 20000000000000 : ℝ))
      (E := (cell12299 ⟨25, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (5200752808359 / 6250000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460870498259 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_26 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (3327102229849 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152178258661 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨26, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (3327102229849 / 4000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152178258661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_27 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41571545406143 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304360476817 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨27, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41571545406143 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304360476817 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_28 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (16621730019907 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576091122453 / 25000000000000 : ℝ))
      (E := (cell12299 ⟨28, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (16621730019907 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576091122453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_29 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41537116787871 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304368500959 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨29, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41537116787871 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304368500959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_30 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (20759960302211 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152186227289 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨30, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (20759960302211 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152186227289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_31 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41502736483471 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304376470149 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨31, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41502736483471 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304376470149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_32 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82971128818301 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152190245777 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨32, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82971128818301 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152190245777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_33 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41468404365673 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304384462351 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨33, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41468404365673 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304384462351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_34 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41451256337333 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460877688581 / 20000000000000 : ℝ))
      (E := (cell12299 ⟨34, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41451256337333 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460877688581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_35 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (5179265038563 / 6250000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304392434861 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨35, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (5179265038563 / 6250000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304392434861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_36 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82833992527281 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304396439631 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨36, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82833992527281 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304396439631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_37 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (20699942093637 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304400458409 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨37, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (20699942093637 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304400458409 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_38 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (82765568128033 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152202216749 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨38, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (82765568128033 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152202216749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_39 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (20682847939279 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288051053031 / 12500000000000 : ℝ))
      (E := (cell12299 ⟨39, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (20682847939279 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288051053031 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

end BstLean.Part263
