import BstLean.Part263Shard2Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part263
open Real

theorem cert12275_0 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (5255165204933 / 6250000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307713464427 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨0, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (5255165204933 / 6250000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307713464427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_1 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (84047528630659 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153858728403 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨1, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (84047528630659 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153858728403 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_2 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (84012439114561 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153860716557 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨2, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (84012439114561 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153860716557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_3 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20994343673423 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576931350759 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨3, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20994343673423 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576931350759 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_4 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83942335331309 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153864687997 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨4, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83942335331309 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153864687997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_5 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41953660495431 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230773341903 / 10000000000000 : ℝ))
      (E := (cell12275 ⟨5, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41953660495431 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (230773341903 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_6 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (10484041454499 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576934341851 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨6, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (10484041454499 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576934341851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_7 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83837367230533 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307741403407 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨7, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83837367230533 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307741403407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_8 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83802427738511 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307745361639 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨8, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83802427738511 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307745361639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_9 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41883756562069 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461549873209 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨9, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41883756562069 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461549873209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_10 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (10466577918977 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461550673301 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨10, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (10466577918977 / 12500000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461550673301 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_11 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83697758386133 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307757370573 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨11, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83697758386133 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307757370573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_12 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83662918191863 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307761327507 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨12, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83662918191863 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307761327507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_13 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41814051366981 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576941340107 / 25000000000000 : ℝ))
      (E := (cell12275 ⟨13, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41814051366981 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (576941340107 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_14 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (20898327994393 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307769301931 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨14, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (20898327994393 / 25000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307769301931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_15 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (16711709177603 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153886666389 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨15, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (16711709177603 / 20000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153886666389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_16 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (41761902215397 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153888642463 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨16, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (41761902215397 / 50000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153888642463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_17 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83489087571593 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153890640311 / 50000000000000 : ℝ))
      (E := (cell12275 ⟨17, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83489087571593 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (1153890640311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_18 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83454395276271 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307785325681 / 100000000000000 : ℝ))
      (E := (cell12275 ⟨18, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83454395276271 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (2307785325681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12275_19 : CellCertificate 12275 (898958463480521 / 10000000000000000 : ℝ) (1711174567335731 / 1000000000000000000 : ℝ) (86486199820361 / 2500000000000000 : ℝ)
    (cell12275 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · norm_num [cell12275]
  · have h := gap_lower (n := 12275) (a := (83419727510867 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461557861851 / 20000000000000 : ℝ))
      (E := (cell12275 ⟨19, by decide⟩).energy) (xi := (86486199820361 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12275 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12275]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12275])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12275) (a := (83419727510867 / 100000000000000 : ℝ)) (b := (167877561649 / 100000000000000 : ℝ)) (q := (461557861851 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12275])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12275]

theorem cert12276_0 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16816525416749 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (72111509903 / 3125000000000 : ℝ))
      (E := (cell12276 ⟨0, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16816525416749 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (72111509903 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_1 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (42023756386407 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307572305359 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨1, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (42023756386407 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307572305359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_2 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (42006211796787 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288447034819 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨2, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (42006211796787 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288447034819 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_3 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (83977359509087 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307580303991 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨3, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (83977359509087 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307580303991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_4 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (5246395030163 / 6250000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153792137727 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨4, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (5246395030163 / 6250000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153792137727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_5 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (83907306477589 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307588259911 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨5, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (83907306477589 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307588259911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_6 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (83872317457673 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153796133133 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨6, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (83872317457673 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153796133133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_7 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41918676693347 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307596245233 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨7, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41918676693347 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307596245233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_8 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (83802414228679 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153800131541 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨8, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (83802414228679 / 100000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153800131541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_9 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41883749973921 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230760426997 / 10000000000000 : ℝ))
      (E := (cell12276 ⟨9, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41883749973921 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230760426997 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_10 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16746522101717 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288451026963 / 12500000000000 : ℝ))
      (E := (cell12276 ⟨10, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16746522101717 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (288451026963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_11 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41848872937749 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307612223813 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨11, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41848872937749 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307612223813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_12 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41831453006677 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153808121813 / 50000000000000 : ℝ))
      (E := (cell12276 ⟨12, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41831453006677 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (1153808121813 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_13 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (10453511360889 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307620224123 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨13, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (10453511360889 / 12500000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307620224123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_14 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (16718660092383 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307624230127 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨14, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (16718660092383 / 20000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307624230127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_15 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (20889633675771 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307628210079 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨15, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (20889633675771 / 25000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307628210079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_16 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41761896788063 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307632170211 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨16, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41761896788063 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307632170211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_17 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41744538523361 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307636174677 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨17, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41744538523361 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307636174677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_18 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (2607949533773 / 3125000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307640171103 / 100000000000000 : ℝ))
      (E := (cell12276 ⟨18, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (2607949533773 / 3125000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (2307640171103 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12276_19 : CellCertificate 12276 (56183039923247 / 625000000000000 : ℝ) (855517564027361 / 500000000000000000 : ℝ) (86478966979371 / 2500000000000000 : ℝ)
    (cell12276 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · norm_num [cell12276]
  · have h := gap_lower (n := 12276) (a := (41709858822103 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230764416499 / 10000000000000 : ℝ))
      (E := (cell12276 ⟨19, by decide⟩).energy) (xi := (86478966979371 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12276 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12276]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12276])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12276) (a := (41709858822103 / 50000000000000 : ℝ)) (b := (20982963027 / 12500000000000 : ℝ)) (q := (230764416499 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12276])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12276]

theorem cert12277_0 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (21020652722801 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307423279581 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨0, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (21020652722801 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307423279581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_1 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (1313242139337 / 1562500000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307427264219 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨1, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (1313242139337 / 1562500000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307427264219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_2 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16802481615029 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307431292197 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨2, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16802481615029 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307431292197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_3 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (20994336081749 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (360536759 / 15625000000 : ℝ))
      (E := (cell12277 ⟨3, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (20994336081749 / 25000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (360536759 / 15625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_4 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83942305636379 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307439285493 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨4, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83942305636379 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307439285493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_5 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41953645983373 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307443269343 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨5, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41953645983373 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307443269343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_6 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83872303281741 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307447217981 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨6, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83872303281741 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307447217981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_7 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83837339545201 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307451255837 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨7, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83837339545201 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307451255837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_8 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83802400721151 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307455217513 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨8, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83802400721151 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307455217513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_9 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (5235467923363 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576864806737 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨9, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (5235467923363 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576864806737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_10 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (41866298833787 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153731617011 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨10, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (41866298833787 / 50000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153731617011 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_11 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (65388854193 / 78125000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (288433398533 / 12500000000000 : ℝ))
      (E := (cell12277 ⟨11, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (65388854193 / 78125000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (288433398533 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_12 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83662893836981 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153735606499 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨12, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83662893836981 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153735606499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_13 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83628079042357 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461495039841 / 20000000000000 : ℝ))
      (E := (cell12277 ⟨13, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83628079042357 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (461495039841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_14 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (8359328894831 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307479153617 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨14, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (8359328894831 / 10000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307479153617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_15 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (16711704704033 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576870799737 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨15, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (16711704704033 / 20000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576870799737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_16 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83523782723427 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153743583577 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨16, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83523782723427 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153743583577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_17 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (4174453326189 / 5000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153745590239 / 50000000000000 : ℝ))
      (E := (cell12277 ⟨17, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (4174453326189 / 5000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (1153745590239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_18 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (5215898430443 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307495128361 / 100000000000000 : ℝ))
      (E := (cell12277 ⟨18, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (5215898430443 / 6250000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (2307495128361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12277_19 : CellCertificate 12277 (449449409372129 / 5000000000000000 : ℝ) (855447855748483 / 500000000000000000 : ℝ) (34588694151279 / 1000000000000000 : ℝ)
    (cell12277 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · norm_num [cell12277]
  · have h := gap_lower (n := 12277) (a := (83419707779391 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576874783163 / 25000000000000 : ℝ))
      (E := (cell12277 ⟨19, by decide⟩).energy) (xi := (34588694151279 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12277 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12277]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12277])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12277) (a := (83419707779391 / 100000000000000 : ℝ)) (b := (1678498491 / 1000000000000 : ℝ)) (q := (576874783163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12277])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12277]

theorem cert12278_0 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10510324337663 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461455670497 / 20000000000000 : ℝ))
      (E := (cell12278 ⟨0, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10510324337663 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461455670497 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_1 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (84047481064921 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576820583347 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨1, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (84047481064921 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576820583347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_2 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10501549069909 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307286300619 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨2, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10501549069909 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307286300619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_3 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83977329147419 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153645160849 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨3, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83977329147419 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153645160849 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_4 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41971145396311 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461458858079 / 20000000000000 : ℝ))
      (E := (cell12278 ⟨4, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41971145396311 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461458858079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_5 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83907277458333 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307298273681 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨5, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83907277458333 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307298273681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_6 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83872289108197 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307302280457 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨6, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83872289108197 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307302280457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_7 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83837325706053 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461461252287 / 20000000000000 : ℝ))
      (E := (cell12278 ⟨7, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83837325706053 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (461461252287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_8 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41901193607963 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576827570721 / 25000000000000 : ℝ))
      (E := (cell12278 ⟨8, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41901193607963 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (576827570721 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_9 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41883736801017 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307314236983 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨9, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41883736801017 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307314236983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_10 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41866292414391 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153659123731 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨10, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41866292414391 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153659123731 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_11 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (2092443021519 / 2500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (92292890557 / 4000000000000 : ℝ))
      (E := (cell12278 ⟨11, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (2092443021519 / 2500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (92292890557 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_12 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (10457860207843 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (3691721977 / 160000000000 : ℝ))
      (E := (cell12278 ⟨12, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (10457860207843 / 12500000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (3691721977 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_13 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (5226754199981 / 6250000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230733022761 / 10000000000000 : ℝ))
      (E := (cell12278 ⟨13, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (5226754199981 / 6250000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (230733022761 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_14 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41796638718379 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307334246681 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨14, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41796638718379 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307334246681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_15 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83558512339257 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307338241271 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨15, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83558512339257 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307338241271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_16 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83523771872697 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307342217617 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨16, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83523771872697 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307342217617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_17 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (41744528001383 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307346181703 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨17, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (41744528001383 / 50000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307346181703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_18 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (83454364695327 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153675098729 / 50000000000000 : ℝ))
      (E := (cell12278 ⟨18, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (83454364695327 / 100000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (1153675098729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12278_19 : CellCertificate 12278 (179773800679257 / 2000000000000000 : ℝ) (1710756317656909 / 1000000000000000000 : ℝ) (172929010032959 / 5000000000000000 : ℝ)
    (cell12278 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · norm_num [cell12278]
  · have h := gap_lower (n := 12278) (a := (4170984895821 / 5000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307354212243 / 100000000000000 : ℝ))
      (E := (cell12278 ⟨19, by decide⟩).energy) (xi := (172929010032959 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12278 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12278]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12278])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12278) (a := (4170984895821 / 5000000000000 : ℝ)) (b := (1678359963 / 1000000000000 : ℝ)) (q := (2307354212243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12278])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12278]

theorem cert12279_0 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (21020644628511 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461426695569 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨0, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (21020644628511 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461426695569 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_1 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (10505933151859 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153568727539 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨1, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (10505933151859 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153568727539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_2 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (42006188522977 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461428295451 / 20000000000000 : ℝ))
      (E := (cell12279 ⟨2, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (42006188522977 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (461428295451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_3 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20994328492589 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576786359613 / 25000000000000 : ℝ))
      (E := (cell12279 ⟨3, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20994328492589 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (576786359613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_4 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (10492784493917 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153574702939 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨4, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (10492784493917 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153574702939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_5 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20976815738087 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307153446573 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨5, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20976815738087 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307153446573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_6 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (1048403436713 / 1250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307157395789 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨6, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (1048403436713 / 1250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307157395789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_7 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83837311869249 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153580717907 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨7, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83837311869249 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153580717907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_8 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (20950593428251 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153582700623 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨8, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (20950593428251 / 25000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153582700623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_9 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41883730216261 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288396177003 / 12500000000000 : ℝ))
      (E := (cell12279 ⟨9, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41883730216261 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (288396177003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_10 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83732571992209 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (92286934881 / 4000000000000 : ℝ))
      (E := (cell12279 ⟨10, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83732571992209 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (92286934881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_11 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (5231106772291 / 6250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307177392777 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨11, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (5231106772291 / 6250000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307177392777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_12 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41831434745321 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153590684777 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨12, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41831434745321 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153590684777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_13 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (10453506919891 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153592683703 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨13, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (10453506919891 / 12500000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153592683703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_14 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41796632963629 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307189335039 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨14, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41796632963629 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307189335039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_15 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41779250580179 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (46143866741 / 2000000000000 : ℝ))
      (E := (cell12279 ⟨15, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41779250580179 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (46143866741 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_16 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83523761023937 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (720999163 / 31250000000 : ℝ))
      (E := (cell12279 ⟨16, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83523761023937 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (720999163 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_17 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83489045483679 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153600676421 / 50000000000000 : ℝ))
      (E := (cell12279 ⟨17, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83489045483679 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (1153600676421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_18 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (83454354505451 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230720532021 / 10000000000000 : ℝ))
      (E := (cell12279 ⟨18, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (83454354505451 / 100000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (230720532021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12279_19 : CellCertificate 12279 (5617744954543 / 62500000000000 : ℝ) (1710616946529 / 1000000000000000 : ℝ) (172914551787713 / 5000000000000000 : ℝ)
    (cell12279 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · norm_num [cell12279]
  · have h := gap_lower (n := 12279) (a := (41709844027647 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307209345553 / 100000000000000 : ℝ))
      (E := (cell12279 ⟨19, by decide⟩).energy) (xi := (172914551787713 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12279 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12279]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12279])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12279) (a := (41709844027647 / 50000000000000 : ℝ)) (b := (20977768227 / 12500000000000 : ℝ)) (q := (2307209345553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12279])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12279]

theorem cert12280_0 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (3363302493177 / 4000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115349432783 / 5000000000000 : ℝ))
      (E := (cell12280 ⟨0, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (3363302493177 / 4000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115349432783 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_1 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (4202372468371 / 5000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153496343541 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨1, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (4202372468371 / 5000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153496343541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_2 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (10501545191899 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576749162167 / 25000000000000 : ℝ))
      (E := (cell12280 ⟨2, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (10501545191899 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (576749162167 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_3 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (16795459759161 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307000665699 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨3, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (16795459759161 / 20000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307000665699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_4 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (2098556527813 / 2500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461400926389 / 20000000000000 : ℝ))
      (E := (cell12280 ⟨4, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (2098556527813 / 2500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461400926389 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_5 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (10488406056099 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (3691213783 / 160000000000 : ℝ))
      (E := (cell12280 ⟨5, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (10488406056099 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (3691213783 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_6 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83872260768269 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153506310943 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨6, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83872260768269 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153506310943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_7 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83837298034789 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230701660519 / 10000000000000 : ℝ))
      (E := (cell12280 ⟨7, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83837298034789 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (230701660519 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_8 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83802360212383 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307020630553 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨8, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83802360212383 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307020630553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_9 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83767447265269 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (46140491803 / 2000000000000 : ℝ))
      (E := (cell12280 ⟨9, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83767447265269 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (46140491803 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_10 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (41866279578927 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307028607713 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨10, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (41866279578927 / 50000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307028607713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_11 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83697695854729 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115351628741 / 5000000000000 : ℝ))
      (E := (cell12280 ⟨11, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83697695854729 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (115351628741 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_12 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (3346514292827 / 4000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307036556741 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨12, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (3346514292827 / 4000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307036556741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_13 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83628043520653 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307040560527 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨13, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83628043520653 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307040560527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_14 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (2612289200619 / 3125000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (144190287061 / 6250000000000 : ℝ))
      (E := (cell12280 ⟨14, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (2612289200619 / 3125000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (144190287061 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_15 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83558489983469 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153524272201 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨15, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83558489983469 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153524272201 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_16 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (10440468772143 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (72095391789 / 3125000000000 : ℝ))
      (E := (cell12280 ⟨16, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (10440468772143 / 12500000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (72095391789 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_17 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83489034966519 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461411303881 / 20000000000000 : ℝ))
      (E := (cell12280 ⟨17, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83489034966519 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (461411303881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_18 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83454344317461 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153530277401 / 50000000000000 : ℝ))
      (E := (cell12280 ⟨18, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83454344317461 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (1153530277401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12280_19 : CellCertificate 12280 (89880938673489 / 1000000000000000 : ℝ) (213809699763461 / 125000000000000000 : ℝ) (345800192039871 / 10000000000000000 : ℝ)
    (cell12280 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · norm_num [cell12280]
  · have h := gap_lower (n := 12280) (a := (83419678196013 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307064532583 / 100000000000000 : ℝ))
      (E := (cell12280 ⟨19, by decide⟩).energy) (xi := (345800192039871 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12280 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12280]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12280])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12280) (a := (83419678196013 / 100000000000000 : ℝ)) (b := (167808297647 / 100000000000000 : ℝ)) (q := (2307064532583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12280])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12280]

theorem cert12281_0 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (21020636536861 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (23068439437 / 1000000000000 : ℝ))
      (E := (cell12281 ⟨0, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (21020636536861 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (23068439437 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_1 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16809486704513 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306847971611 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨1, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16809486704513 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306847971611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_2 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (10501543253373 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306851930487 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨2, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (10501543253373 / 12500000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306851930487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_3 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41988641811883 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306855945607 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨3, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41988641811883 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306855945607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_4 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41971123138087 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (115342995537 / 5000000000000 : ℝ))
      (E := (cell12281 ⟨4, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41971123138087 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (115342995537 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_5 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (5244202121729 / 6250000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461372790147 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨5, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (5244202121729 / 6250000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461372790147 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_6 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83872246601883 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576716975211 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨6, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83872246601883 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576716975211 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_7 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83837284202673 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153435942711 / 50000000000000 : ℝ))
      (E := (cell12281 ⟨7, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83837284202673 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (1153435942711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_8 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (5237646669629 / 6250000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306875912853 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨8, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (5237646669629 / 6250000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306875912853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_9 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20941858525069 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144179992207 / 6250000000000 : ℝ))
      (E := (cell12281 ⟨9, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20941858525069 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (144179992207 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_10 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20933136581429 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306883896529 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨10, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20933136581429 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306883896529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_11 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41848841677489 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306887868079 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨11, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41848841677489 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306887868079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_12 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41831422576421 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461378371047 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨12, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41831422576421 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461378371047 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_13 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (8362803168427 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461379173009 / 20000000000000 : ℝ))
      (E := (cell12281 ⟨13, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (8362803168427 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (461379173009 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_14 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (8359324291441 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306899846211 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨14, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (8359324291441 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306899846211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_15 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (8355847880859 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306903863329 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨15, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (8355847880859 / 10000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306903863329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_16 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (83523739332319 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (28836348307 / 1250000000000 : ℝ))
      (E := (cell12281 ⟨16, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (83523739332319 / 100000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (28836348307 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_17 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (16697804890257 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306911855889 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨17, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (16697804890257 / 20000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306911855889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_18 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (20863583532839 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576728960763 / 25000000000000 : ℝ))
      (E := (cell12281 ⟨18, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (20863583532839 / 25000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (576728960763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12281_19 : CellCertificate 12281 (898779585419161 / 10000000000000000 : ℝ) (53448071012107 / 31250000000000000 : ℝ) (345771285457811 / 10000000000000000 : ℝ)
    (cell12281 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · norm_num [cell12281]
  · have h := gap_lower (n := 12281) (a := (41709834169287 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306919831549 / 100000000000000 : ℝ))
      (E := (cell12281 ⟨19, by decide⟩).energy) (xi := (345771285457811 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12281 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12281]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12281])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12281) (a := (41709834169287 / 50000000000000 : ℝ)) (b := (10487153237 / 6250000000000 : ℝ)) (q := (2306919831549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12281])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12281]

theorem cert12282_0 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (84082529968103 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576674835491 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨0, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (84082529968103 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576674835491 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_1 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (84047417680307 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153351654333 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨1, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (84047417680307 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153351654333 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_2 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (84012330521329 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288338415339 / 12500000000000 : ℝ))
      (E := (cell12282 ⟨2, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (84012330521329 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288338415339 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_3 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83977268454239 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306711336011 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨3, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83977268454239 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306711336011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_4 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83942231442297 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (57667882503 / 2500000000000 : ℝ))
      (E := (cell12282 ⟨4, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83942231442297 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (57667882503 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_5 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41953609724481 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306719282007 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨5, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41953609724481 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306719282007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_6 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41936116218941 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288340411321 / 12500000000000 : ℝ))
      (E := (cell12282 ⟨6, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41936116218941 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (288340411321 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_7 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (838372703729 / 1000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306727276511 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨7, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (838372703729 / 1000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306727276511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_8 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41901166609023 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576682812037 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨8, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41901166609023 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576682812037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_9 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41883710468771 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230673527151 / 10000000000000 : ℝ))
      (E := (cell12282 ⟨9, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41883710468771 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (230673527151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_10 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (20933133373949 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306739238471 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨10, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (20933133373949 / 25000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306739238471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_11 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41848835428701 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576685818139 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨11, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41848835428701 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576685818139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_12 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41831416493571 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576686816259 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨12, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41831416493571 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576686816259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_13 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83628019849979 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306751222889 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨13, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83628019849979 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306751222889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_14 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (41796615705531 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306755210933 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨14, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (41796615705531 / 50000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306755210933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_15 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83558467635719 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576689808929 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨15, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83558467635719 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576689808929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_16 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83523728489461 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306763187257 / 100000000000000 : ℝ))
      (E := (cell12282 ⟨16, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83523728489461 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (2306763187257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_17 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83489013937977 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153383593899 / 50000000000000 : ℝ))
      (E := (cell12282 ⟨17, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83489013937977 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (1153383593899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_18 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (16690864789427 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (7208659953 / 312500000000 : ℝ))
      (E := (cell12282 ⟨18, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (16690864789427 / 20000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (7208659953 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12282_19 : CellCertificate 12282 (898749788778541 / 10000000000000000 : ℝ) (855099484681331 / 500000000000000000 : ℝ) (10804449494619 / 312500000000000 : ℝ)
    (cell12282 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · norm_num [cell12282]
  · have h := gap_lower (n := 12282) (a := (83419658482979 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576693796059 / 25000000000000 : ℝ))
      (E := (cell12282 ⟨19, by decide⟩).energy) (xi := (10804449494619 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12282 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12282]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12282])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12282) (a := (83419658482979 / 100000000000000 : ℝ)) (b := (41945152063 / 25000000000000 : ℝ)) (q := (576693796059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12282])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12282]

theorem cert12283_0 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (84082513791399 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306554792691 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨0, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (84082513791399 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306554792691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_1 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (84047401840643 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153279378021 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨1, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (84047401840643 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153279378021 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_2 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (21003078754557 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153281383767 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨2, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (21003078754557 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153281383767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_3 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41988626643611 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306566779079 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨3, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41988626643611 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306566779079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_4 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83942216610889 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288321342779 / 12500000000000 : ℝ))
      (E := (cell12283 ⟨4, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83942216610889 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288321342779 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_5 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83907204952687 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306574723959 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨5, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83907204952687 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306574723959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_6 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41936109138133 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576644683289 / 25000000000000 : ℝ))
      (E := (cell12283 ⟨6, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41936109138133 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (576644683289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_7 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83837256545469 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306582720531 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨7, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83837256545469 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306582720531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_8 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83802319724329 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288323336799 / 12500000000000 : ℝ))
      (E := (cell12283 ⟨8, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83802319724329 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288323336799 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_9 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41883703888533 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153295360387 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨9, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41883703888533 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153295360387 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_10 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (20933130167023 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288324336443 / 12500000000000 : ℝ))
      (E := (cell12283 ⟨10, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (20933130167023 / 25000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (288324336443 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_11 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83697658362001 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153299336103 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨11, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83697658362001 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153299336103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_12 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (3346512832943 / 4000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153301335027 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨12, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (3346512832943 / 4000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153301335027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_13 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (4181400400889 / 5000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306606692133 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨13, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (4181400400889 / 5000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306606692133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_14 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83593219909763 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461322137429 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨14, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83593219909763 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461322137429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_15 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (10444807058107 / 12500000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153307330783 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨15, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (10444807058107 / 12500000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153307330783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_16 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (8352371764857 / 10000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461323735953 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨16, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (8352371764857 / 10000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461323735953 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_17 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41744501713297 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306622631467 / 100000000000000 : ℝ))
      (E := (cell12283 ⟨17, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41744501713297 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (2306622631467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_18 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (41727156882399 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461325327743 / 20000000000000 : ℝ))
      (E := (cell12283 ⟨18, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (41727156882399 / 50000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (461325327743 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12283_19 : CellCertificate 12283 (898719996811879 / 10000000000000000 : ℝ) (106878730564241 / 62500000000000000 : ℝ) (345713487148419 / 10000000000000000 : ℝ)
    (cell12283 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · norm_num [cell12283]
  · have h := gap_lower (n := 12283) (a := (83419648629227 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153315324431 / 50000000000000 : ℝ))
      (E := (cell12283 ⟨19, by decide⟩).energy) (xi := (345713487148419 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12283 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12283]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12283])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12283) (a := (83419648629227 / 100000000000000 : ℝ)) (b := (10485422939 / 6250000000000 : ℝ)) (q := (1153315324431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12283])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12283]

theorem cert12284_0 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (21020624404333 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306410295883 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨0, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (21020624404333 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306410295883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_1 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (3361895440143 / 4000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461282862747 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨1, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (3361895440143 / 4000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461282862747 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_2 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (1050153743971 / 1250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461283664553 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨2, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (1050153743971 / 1250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461283664553 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_3 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20994309530679 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306422274811 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨3, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20994309530679 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306422274811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_4 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83942201781949 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153213147467 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨4, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83942201781949 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153213147467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_5 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83907190458837 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306430276593 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨5, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83907190458837 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306430276593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_6 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83872204117033 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306434286517 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨6, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83872204117033 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306434286517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_7 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (4191862136019 / 5000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576609568853 / 25000000000000 : ℝ))
      (E := (cell12284 ⟨7, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (4191862136019 / 5000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576609568853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_8 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83802306232911 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306442251589 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨8, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83802306232911 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306442251589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_9 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (2617731081839 / 3125000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153223111551 / 50000000000000 : ℝ))
      (E := (cell12284 ⟨9, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (2617731081839 / 3125000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (1153223111551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_10 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20933126960651 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306450255749 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨10, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20933126960651 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306450255749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_11 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41848822934387 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306454241101 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨11, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41848822934387 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306454241101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_12 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83662808662141 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306458244429 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨12, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83662808662141 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306458244429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_13 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83627996187671 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306462214707 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨13, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83627996187671 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306462214707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_14 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (41796604205257 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306466216753 / 100000000000000 : ℝ))
      (E := (cell12284 ⟨14, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (41796604205257 / 50000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (2306466216753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_15 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (83558445296001 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461294039799 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨15, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (83558445296001 / 100000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461294039799 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_16 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (16704741361929 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (115323708383 / 5000000000000 : ℝ))
      (E := (cell12284 ⟨16, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (16704741361929 / 20000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (115323708383 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_17 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (5218062057321 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461295637379 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨17, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (5218062057321 / 6250000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461295637379 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_18 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (10431787948043 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576620536533 / 25000000000000 : ℝ))
      (E := (cell12284 ⟨18, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (10431787948043 / 12500000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (576620536533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12284_19 : CellCertificate 12284 (898690209518021 / 10000000000000000 : ℝ) (1709920431377463 / 1000000000000000000 : ℝ) (345684595418207 / 10000000000000000 : ℝ)
    (cell12284 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · norm_num [cell12284]
  · have h := gap_lower (n := 12284) (a := (20854909694329 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461297233443 / 20000000000000 : ℝ))
      (E := (cell12284 ⟨19, by decide⟩).energy) (xi := (345684595418207 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12284 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12284]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12284])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12284) (a := (20854909694329 / 25000000000000 : ℝ)) (b := (167752928109 / 100000000000000 : ℝ)) (q := (461297233443 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12284])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12284]

theorem cert12285_0 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (84082481445903 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153132954651 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨0, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (84082481445903 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153132954651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_1 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (84047370169101 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306269923961 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨1, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (84047370169101 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306269923961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_2 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (84012284019683 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461254786119 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨2, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (84012284019683 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461254786119 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_3 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83977222960719 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461255576209 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨3, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83977222960719 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461255576209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_4 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (20985546738869 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306281900369 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨4, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (20985546738869 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306281900369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_5 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83907175967413 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (92251435281 / 4000000000000 : ℝ))
      (E := (cell12285 ⟨5, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83907175967413 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (92251435281 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_6 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83872189960183 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306289892743 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨6, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83872189960183 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306289892743 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_7 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83837228897631 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306293883227 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨7, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83837228897631 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306293883227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_8 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (5237643296487 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461259572357 / 20000000000000 : ℝ))
      (E := (cell12285 ⟨8, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (5237643296487 / 6250000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (461259572357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_9 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (10470922682861 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (288287729559 / 12500000000000 : ℝ))
      (E := (cell12285 ⟨9, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (10470922682861 / 12500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (288287729559 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_10 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83732495019331 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153152907543 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨10, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83732495019331 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153152907543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_11 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (2092440834443 / 2500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576577451293 / 25000000000000 : ℝ))
      (E := (cell12285 ⟨11, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (2092440834443 / 2500000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (576577451293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_12 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41831398251419 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306313814023 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨12, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41831398251419 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306313814023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_13 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (20906996089913 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153158895307 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨13, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (20906996089913 / 25000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153158895307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_14 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83593196913313 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306321799759 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨14, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83593196913313 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306321799759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_15 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41779217064577 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306325789887 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨15, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41779217064577 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306325789887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_16 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41761847986343 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153164912683 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨16, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41761847986343 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153164912683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_17 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (41744491204801 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306333795919 / 100000000000000 : ℝ))
      (E := (cell12285 ⟨17, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (41744491204801 / 50000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (2306333795919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_18 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83454293405773 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153168882699 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨18, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83454293405773 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153168882699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12285_19 : CellCertificate 12285 (449330213447909 / 5000000000000000 : ℝ) (854890598202971 / 500000000000000000 : ℝ) (172827854317867 / 5000000000000000 : ℝ)
    (cell12285 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · norm_num [cell12285]
  · have h := gap_lower (n := 12285) (a := (83419628927247 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153170898753 / 50000000000000 : ℝ))
      (E := (cell12285 ⟨19, by decide⟩).energy) (xi := (172827854317867 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12285 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12285]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12285])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12285) (a := (83419628927247 / 100000000000000 : ℝ)) (b := (167739091507 / 100000000000000 : ℝ)) (q := (1153170898753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12285])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12285]

theorem cert12286_0 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (84082465277109 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153060816479 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨0, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (84082465277109 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153060816479 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_1 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (4202367716861 / 5000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153062793361 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨1, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (4202367716861 / 5000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153062793361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_2 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (42006134262119 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306129591027 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨2, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (42006134262119 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306129591027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_3 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (5248575487577 / 6250000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306133597783 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨3, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (5248575487577 / 6250000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306133597783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_4 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (8394217213147 / 10000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306137558539 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨4, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (8394217213147 / 10000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306137558539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_5 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41953580739207 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115307077013 / 5000000000000 : ℝ))
      (E := (cell12286 ⟨5, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41953580739207 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115307077013 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_6 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20968043951429 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153072775919 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨6, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20968043951429 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153072775919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_7 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10479651884653 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288268692997 / 12500000000000 : ℝ))
      (E := (cell12286 ⟨7, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10479651884653 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288268692997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_8 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83802279256971 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288269190623 / 12500000000000 : ℝ))
      (E := (cell12286 ⟨8, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83802279256971 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (288269190623 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_9 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (1308865129831 / 1562500000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306157560889 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨9, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (1308865129831 / 1562500000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306157560889 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_10 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (41866241099137 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153080771779 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨10, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (41866241099137 / 50000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153080771779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_11 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (2092440522221 / 2500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306165538491 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨11, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (2092440522221 / 2500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306165538491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_12 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83662784345667 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306169494933 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨12, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83662784345667 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306169494933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_13 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20906993133431 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576543369481 / 25000000000000 : ℝ))
      (E := (cell12286 ⟨13, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20906993133431 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (576543369481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_14 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (83593185418161 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115308874713 / 5000000000000 : ℝ))
      (E := (cell12286 ⟨14, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (83593185418161 / 100000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (115308874713 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_15 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10444802870539 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153090746183 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨15, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10444802870539 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153090746183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_16 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (20880921284423 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153092739233 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨16, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (20880921284423 / 25000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153092739233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_17 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (10436121487999 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306189458543 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨17, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (10436121487999 / 12500000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306189458543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_18 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (16690856645817 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153096748259 / 50000000000000 : ℝ))
      (E := (cell12286 ⟨18, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (16690856645817 / 20000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (1153096748259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12286_19 : CellCertificate 12286 (449315324472059 / 5000000000000000 : ℝ) (1709641984107753 / 1000000000000000000 : ℝ) (345626826799561 / 10000000000000000 : ℝ)
    (cell12286 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · norm_num [cell12286]
  · have h := gap_lower (n := 12286) (a := (4170980953951 / 5000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306197481529 / 100000000000000 : ℝ))
      (E := (cell12286 ⟨19, by decide⟩).energy) (xi := (345626826799561 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12286 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12286]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12286])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12286) (a := (4170980953951 / 5000000000000 : ℝ)) (b := (33545051443 / 20000000000000 : ℝ)) (q := (2306197481529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12286])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12286]

theorem cert12287_0 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (1681648982219 / 2000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461195470263 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨0, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (1681648982219 / 2000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461195470263 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_1 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (84047338507933 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305981359807 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨1, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (84047338507933 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305981359807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_2 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (84012253031343 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (3689576579 / 160000000000 : ℝ))
      (E := (cell12287 ⟨2, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (84012253031343 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (3689576579 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_3 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20994298161063 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305989367191 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨3, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20994298161063 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305989367191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_4 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (8394215730993 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461198665461 / 20000000000000 : ℝ))
      (E := (cell12287 ⟨4, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (8394215730993 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (461198665461 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_5 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41953573495919 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305997309181 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨5, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41953573495919 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2305997309181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_6 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83872161653631 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306001321709 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨6, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83872161653631 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306001321709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_7 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20959300314789 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306005315593 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨7, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20959300314789 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306005315593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_8 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83802265772449 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306009299139 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨8, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83802265772449 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306009299139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_9 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (10470919394717 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153006640199 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨9, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (10470919394717 / 12500000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153006640199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_10 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (8373246937943 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306017267167 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨10, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (8373246937943 / 10000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306017267167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_11 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20924402100533 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306021266989 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨11, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20924402100533 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306021266989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_12 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83662772190627 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306025287157 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨12, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83662772190627 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306025287157 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_13 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (20906990177471 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306029276641 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨13, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (20906990177471 / 25000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306029276641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_14 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (1306143342579 / 1562500000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153016621081 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨14, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (1306143342579 / 1562500000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153016621081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_15 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83558411801477 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (230603724831 / 10000000000000 : ℝ))
      (E := (cell12287 ⟨15, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83558411801477 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (230603724831 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_16 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (41761837152331 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306041243239 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨16, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (41761837152331 / 50000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306041243239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_17 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (16697792280061 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306045232929 / 100000000000000 : ℝ))
      (E := (cell12287 ⟨17, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (16697792280061 / 20000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (2306045232929 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_18 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83454273054279 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153024611557 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨18, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83454273054279 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153024611557 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12287_19 : CellCertificate 12287 (89860087566177 / 1000000000000000 : ℝ) (854751397238679 / 500000000000000000 : ℝ) (345597949908251 / 10000000000000000 : ℝ)
    (cell12287 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · norm_num [cell12287]
  · have h := gap_lower (n := 12287) (a := (83419609232633 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153026609641 / 50000000000000 : ℝ))
      (E := (cell12287 ⟨19, by decide⟩).energy) (xi := (345597949908251 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12287 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12287]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12287])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12287) (a := (83419609232633 / 100000000000000 : ℝ)) (b := (33542285047 / 20000000000000 : ℝ)) (q := (1153026609641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12287])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12287]

theorem cert12288_0 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (84082432947427 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152916618837 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨0, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (84082432947427 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152916618837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_1 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (42023661340619 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305837185429 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨1, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (42023661340619 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305837185429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_2 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (42006118770499 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305841185327 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨2, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (42006118770499 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305841185327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_3 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83977177489781 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230584518927 / 10000000000000 : ℝ))
      (E := (cell12288 ⟨3, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83977177489781 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230584518927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_4 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (10492767811357 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305849206669 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨4, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (10492767811357 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305849206669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_5 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41953566253843 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230585318879 / 10000000000000 : ℝ))
      (E := (cell12288 ⟨5, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41953566253843 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (230585318879 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_6 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83872147503927 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576464286113 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨6, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83872147503927 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576464286113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_7 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83837187443427 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576465285037 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨7, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83837187443427 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576465285037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_8 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (5237640768139 / 6250000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576466296063 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨8, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (5237640768139 / 6250000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576466296063 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_9 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83767342008543 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305869168933 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨9, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83767342008543 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305869168933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_10 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (209331141407 / 250000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152936579957 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨10, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (209331141407 / 250000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152936579957 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_11 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (20924398979399 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576469276679 / 25000000000000 : ℝ))
      (E := (cell12288 ⟨11, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (20924398979399 / 25000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (576469276679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_12 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83662760037717 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305881132653 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨12, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83662760037717 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305881132653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_13 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83627948888133 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461177025739 / 20000000000000 : ℝ))
      (E := (cell12288 ⟨13, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83627948888133 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (461177025739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_14 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41796581216999 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305889101561 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨14, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41796581216999 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305889101561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_15 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (10444800080081 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305893115841 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨15, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (10444800080081 / 12500000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305893115841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_16 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83523663473597 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305897119689 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨16, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83523663473597 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305897119689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_17 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (83488950898541 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305901119083 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨17, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (83488950898541 / 100000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305901119083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_18 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41727131440677 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152952530783 / 50000000000000 : ℝ))
      (E := (cell12288 ⟨18, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41727131440677 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (1152952530783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12288_19 : CellCertificate 12288 (7188568856381 / 80000000000000 : ℝ) (1709363627509221 / 1000000000000000000 : ℝ) (345569077960369 / 10000000000000000 : ℝ)
    (cell12288 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · norm_num [cell12288]
  · have h := gap_lower (n := 12288) (a := (41709799694043 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305909068981 / 100000000000000 : ℝ))
      (E := (cell12288 ⟨19, by decide⟩).energy) (xi := (345569077960369 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12288 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12288]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12288])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12288) (a := (41709799694043 / 50000000000000 : ℝ)) (b := (33539519113 / 20000000000000 : ℝ)) (q := (2305909068981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12288])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12288]

theorem cert12289_0 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (84082416786537 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115284455937 / 5000000000000 : ℝ))
      (E := (cell12289 ⟨0, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (84082416786537 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115284455937 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_1 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (42023653428567 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152846560691 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨1, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (42023653428567 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152846560691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_2 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (42006111026601 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305697119199 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨2, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (42006111026601 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305697119199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_3 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (10497145292227 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115285056093 / 5000000000000 : ℝ))
      (E := (cell12289 ⟨3, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (10497145292227 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115285056093 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_4 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41971063837123 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92228205551 / 4000000000000 : ℝ))
      (E := (cell12289 ⟨4, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41971063837123 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92228205551 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_5 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83907118025957 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152854560603 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨5, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83907118025957 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152854560603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_6 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (20968033339151 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288214134747 / 12500000000000 : ℝ))
      (E := (cell12289 ⟨6, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (20968033339151 / 25000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288214134747 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_7 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41918586815019 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305717075573 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨7, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41918586815019 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305717075573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_8 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16760447762059 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115286053221 / 5000000000000 : ℝ))
      (E := (cell12289 ⟨8, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16760447762059 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (115286053221 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_9 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (41883664430803 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305725052563 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨9, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (41883664430803 / 50000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305725052563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_10 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (2616638867137 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (11528645239 / 500000000000 : ℝ))
      (E := (cell12289 ⟨10, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (2616638867137 / 3125000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (11528645239 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_11 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83697583435231 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305733057673 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨11, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83697583435231 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305733057673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_12 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (10457843485867 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152868515711 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨12, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (10457843485867 / 12500000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152868515711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_13 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (8362793706847 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288217629261 / 12500000000000 : ℝ))
      (E := (cell12289 ⟨13, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (8362793706847 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (288217629261 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_14 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83593150944987 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152872507183 / 50000000000000 : ℝ))
      (E := (cell12289 ⟨14, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83593150944987 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (1152872507183 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_15 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83558389481823 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (461149807369 / 20000000000000 : ℝ))
      (E := (cell12289 ⟨15, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83558389481823 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (461149807369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_16 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (16704730528899 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305753049677 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨16, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (16704730528899 / 20000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305753049677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_17 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83488940398699 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92230280027 / 4000000000000 : ℝ))
      (E := (cell12289 ⟨17, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83488940398699 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (92230280027 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_18 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (8345425271031 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576440252969 / 25000000000000 : ℝ))
      (E := (cell12289 ⟨18, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (8345425271031 / 10000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (576440252969 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12289_19 : CellCertificate 12289 (898541343100531 / 10000000000000000 : ℝ) (1709224483197809 / 1000000000000000000 : ℝ) (4319252636931 / 125000000000000 : ℝ)
    (cell12289 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · norm_num [cell12289]
  · have h := gap_lower (n := 12289) (a := (83419589545379 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305765030627 / 100000000000000 : ℝ))
      (E := (cell12289 ⟨19, by decide⟩).energy) (xi := (4319252636931 / 125000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12289 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12289]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12289])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12289) (a := (83419589545379 / 100000000000000 : ℝ)) (b := (41920942051 / 25000000000000 : ℝ)) (q := (2305765030627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12289])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12289]

theorem cert12290_0 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (84082400628281 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576386291953 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨0, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (84082400628281 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576386291953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_1 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (42023645517811 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (144096822979 / 6250000000000 : ℝ))
      (E := (cell12290 ⟨1, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (42023645517811 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (144096822979 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_2 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (21003051641989 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305553105677 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨2, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (21003051641989 / 25000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305553105677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_3 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41988573594179 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576389276781 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨3, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41988573594179 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576389276781 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_4 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83942112860101 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305561123621 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨4, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83942112860101 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305561123621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_5 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (1678142070933 / 2000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305565106431 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨5, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (1678142070933 / 2000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305565106431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_6 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83872119211661 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152784561141 / 50000000000000 : ℝ))
      (E := (cell12290 ⟨6, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83872119211661 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (1152784561141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_7 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41918579909493 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (115278653197 / 5000000000000 : ℝ))
      (E := (cell12290 ⟨7, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41918579909493 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (115278653197 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_8 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (10475278166583 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576394263887 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨8, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (10475278166583 / 12500000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576394263887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_9 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83767315716923 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288197638153 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨9, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83767315716923 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288197638153 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_10 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (4186621546809 / 5000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305585046829 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨10, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (4186621546809 / 5000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305585046829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_11 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41848785477519 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305589061837 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨11, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41848785477519 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305589061837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_12 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (16732547147657 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288199130189 / 12500000000000 : ℝ))
      (E := (cell12290 ⟨12, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (16732547147657 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (288199130189 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_13 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (16725585050179 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576399262723 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨13, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (16725585050179 / 20000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576399262723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_14 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (41796569729011 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305601038671 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨14, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (41796569729011 / 50000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305601038671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_15 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83558378325003 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305605011321 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨15, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83558378325003 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305605011321 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_16 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83523641817357 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305609033203 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨16, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83523641817357 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305609033203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_17 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83488929900779 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576403248509 / 25000000000000 : ℝ))
      (E := (cell12290 ⟨17, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83488929900779 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (576403248509 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_18 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83454242541147 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461123403171 / 20000000000000 : ℝ))
      (E := (cell12290 ⟨18, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83454242541147 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (461123403171 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12290_19 : CellCertificate 12290 (898511583819341 / 10000000000000000 : ℝ) (427271340384397 / 250000000000000000 : ℝ) (86377837222287 / 2500000000000000 : ℝ)
    (cell12290 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · norm_num [cell12290]
  · have h := gap_lower (n := 12290) (a := (83419579704511 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305620987797 / 100000000000000 : ℝ))
      (E := (cell12290 ⟨19, by decide⟩).energy) (xi := (86377837222287 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12290 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12290]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12290])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12290) (a := (83419579704511 / 100000000000000 : ℝ)) (b := (10479371447 / 6250000000000 : ℝ)) (q := (2305620987797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12290])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12290]

theorem cert12291_0 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (84082384472657 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461080242319 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨0, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (84082384472657 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461080242319 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_1 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (840472752167 / 1000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (23054052087 / 1000000000000 : ℝ))
      (E := (cell12291 ⟨1, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (840472752167 / 1000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (23054052087 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_2 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (84012191085257 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (115270460129 / 5000000000000 : ℝ))
      (E := (cell12291 ⟨2, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (84012191085257 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (115270460129 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_3 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41988566020703 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152706601451 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨3, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41988566020703 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152706601451 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_4 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (4197104902421 / 5000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305417219071 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨4, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (4197104902421 / 5000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305417219071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_5 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (20976772267441 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305421202351 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨5, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (20976772267441 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305421202351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_6 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41936052534549 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152712580779 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨6, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41936052534549 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152712580779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_7 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (2619910812821 / 3125000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152714581591 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨7, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (2619910812821 / 3125000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152714581591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_8 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83802211857327 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152716578821 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨8, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83802211857327 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152716578821 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_9 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83767302574493 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288179644123 / 12500000000000 : ℝ))
      (E := (cell12291 ⟨9, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83767302574493 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (288179644123 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_10 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (20933104531547 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152720578501 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨10, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (20933104531547 / 25000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152720578501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_11 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41848779238507 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576361279803 / 25000000000000 : ℝ))
      (E := (cell12291 ⟨11, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41848779238507 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (576361279803 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_12 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83662723591763 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152724581463 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨12, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83662723591763 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152724581463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_13 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83627913435407 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152726560519 / 50000000000000 : ℝ))
      (E := (cell12291 ⟨13, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83627913435407 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (1152726560519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_14 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (41796563986551 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461091423277 / 20000000000000 : ℝ))
      (E := (cell12291 ⟨14, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (41796563986551 / 50000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (461091423277 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_15 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83558367170187 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305461097389 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨15, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83558367170187 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305461097389 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_16 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83523630992181 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305465128411 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨16, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83523630992181 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305465128411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_17 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83488919404781 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (72045909349 / 3125000000000 : ℝ))
      (E := (cell12291 ⟨17, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83488919404781 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (72045909349 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_18 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83454232373863 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305473073509 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨18, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83454232373863 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305473073509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12291_19 : CellCertificate 12291 (179696365840581 / 2000000000000000 : ℝ) (1708946262523029 / 1000000000000000000 : ℝ) (17274124588147 / 500000000000000 : ℝ)
    (cell12291 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · norm_num [cell12291]
  · have h := gap_lower (n := 12291) (a := (83419569865483 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305477115129 / 100000000000000 : ℝ))
      (E := (cell12291 ⟨19, by decide⟩).energy) (xi := (17274124588147 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12291 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12291]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12291])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12291) (a := (83419569865483 / 100000000000000 : ℝ)) (b := (20957015051 / 12500000000000 : ℝ)) (q := (2305477115129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12291])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12291]

theorem cert12292_0 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (42041184159833 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (115262868281 / 5000000000000 : ℝ))
      (E := (cell12292 ⟨0, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (42041184159833 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (115262868281 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_1 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (84047259400367 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305261360071 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨1, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (84047259400367 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305261360071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_2 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (42006087802553 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152632676047 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨2, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (42006087802553 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152632676047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_3 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (262428490303 / 312500000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305269351357 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨3, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (262428490303 / 312500000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305269351357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_4 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41971041619601 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461054673453 / 20000000000000 : ℝ))
      (E := (cell12292 ⟨4, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41971041619601 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (461054673453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_5 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (839070745953 / 1000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305277351081 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨5, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (839070745953 / 1000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305277351081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_6 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41936045464457 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152640684763 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨6, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41936045464457 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152640684763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_7 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (16767426440779 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (288160664421 / 12500000000000 : ℝ))
      (E := (cell12292 ⟨7, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (16767426440779 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (288160664421 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_8 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (41901099192143 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152644656373 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨8, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (41901099192143 / 50000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152644656373 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_9 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83767289434317 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305293311799 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨9, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83767289434317 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305293311799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_10 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83732405318407 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305297320319 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨10, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83732405318407 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305297320319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_11 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83697546001161 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (115265064391 / 5000000000000 : ℝ))
      (E := (cell12292 ⟨11, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83697546001161 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (115265064391 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_12 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83662711447369 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144081579973 / 6250000000000 : ℝ))
      (E := (cell12292 ⟨12, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83662711447369 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (144081579973 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_13 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (16725580324401 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305309302599 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨13, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (16725580324401 / 20000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305309302599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_14 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83593116490227 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576328326401 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨14, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83593116490227 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576328326401 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_15 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (668466848139 / 800000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (46106345901 / 2000000000000 : ℝ))
      (E := (cell12292 ⟨15, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (668466848139 / 800000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (46106345901 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_16 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83523620168967 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305321277161 / 100000000000000 : ℝ))
      (E := (cell12292 ⟨16, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83523620168967 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (2305321277161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_17 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (83488908910703 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576331314477 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨17, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (83488908910703 / 100000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576331314477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_18 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (4172711110423 / 5000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152664621511 / 50000000000000 : ℝ))
      (E := (cell12292 ⟨18, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (4172711110423 / 5000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (1152664621511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12292_19 : CellCertificate 12292 (449226039625037 / 5000000000000000 : ℝ) (1708807186148601 / 1000000000000000000 : ℝ) (345453639574423 / 10000000000000000 : ℝ)
    (cell12292 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · norm_num [cell12292]
  · have h := gap_lower (n := 12292) (a := (20854890007073 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576333309497 / 25000000000000 : ℝ))
      (E := (cell12292 ⟨19, by decide⟩).energy) (xi := (345453639574423 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12292 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12292]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12292])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12292) (a := (20854890007073 / 25000000000000 : ℝ)) (b := (41910574993 / 25000000000000 : ℝ)) (q := (576333309497 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12292])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12292]

theorem cert12293_0 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (42041176084653 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305113629891 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨0, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (42041176084653 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305113629891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_1 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (1313238181041 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (144069851361 / 6250000000000 : ℝ))
      (E := (cell12293 ⟨1, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (1313238181041 / 1562500000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (144069851361 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_2 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (42006080063751 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305121612033 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨2, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (42006080063751 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305121612033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_3 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41988550877509 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288140701291 / 12500000000000 : ℝ))
      (E := (cell12293 ⟨3, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41988550877509 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288140701291 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_4 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41971034216223 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152564784103 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨4, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41971034216223 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152564784103 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_5 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (10488382515407 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305133610507 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨5, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (10488382515407 / 12500000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305133610507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_6 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (20968019197777 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152568786233 / 50000000000000 : ℝ))
      (E := (cell12293 ⟨6, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (20968019197777 / 25000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (1152568786233 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_7 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (16767423679971 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230514157843 / 10000000000000 : ℝ))
      (E := (cell12293 ⟨7, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (16767423679971 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230514157843 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_8 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (4190109245677 / 5000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (36017899669 / 1562500000000 : ℝ))
      (E := (cell12293 ⟨8, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (4190109245677 / 5000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (36017899669 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_9 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41883638148197 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230514958167 / 10000000000000 : ℝ))
      (E := (cell12293 ⟨9, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41883638148197 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230514958167 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_10 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41866196256419 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305153536781 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨10, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41866196256419 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305153536781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_11 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83697533527477 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461031513533 / 20000000000000 : ℝ))
      (E := (cell12293 ⟨11, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83697533527477 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (461031513533 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_12 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41831349652551 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305161507537 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨12, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41831349652551 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305161507537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_13 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83627889810689 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (72036423047 / 3125000000000 : ℝ))
      (E := (cell12293 ⟨13, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83627889810689 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (72036423047 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_14 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83593105009397 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288146193529 / 12500000000000 : ℝ))
      (E := (cell12293 ⟨14, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83593105009397 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (288146193529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_15 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (41779172433283 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230517348807 / 10000000000000 : ℝ))
      (E := (cell12293 ⟨15, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (41779172433283 / 50000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (230517348807 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_16 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (16704721869543 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576294369863 / 25000000000000 : ℝ))
      (E := (cell12293 ⟨16, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (16704721869543 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (576294369863 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_17 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (16697779683709 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305181470257 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨17, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (16697779683709 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305181470257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_18 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (16690842408987 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305185466211 / 100000000000000 : ℝ))
      (E := (cell12293 ⟨18, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (16690842408987 / 20000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2305185466211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12293_19 : CellCertificate 12293 (898422333959701 / 10000000000000000 : ℝ) (1708668132408779 / 1000000000000000000 : ℝ) (69084958464433 / 2000000000000000 : ℝ)
    (cell12293 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · norm_num [cell12293]
  · have h := gap_lower (n := 12293) (a := (83419550192939 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2881486841 / 125000000000 : ℝ))
      (E := (cell12293 ⟨19, by decide⟩).energy) (xi := (69084958464433 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12293 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12293]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12293])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12293) (a := (83419550192939 / 100000000000000 : ℝ)) (b := (41907120461 / 25000000000000 : ℝ)) (q := (2881486841 / 125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12293])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12293]

theorem cert12294_0 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (84082336021577 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576242486661 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨0, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (84082336021577 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576242486661 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_1 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (8404722777547 / 10000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230497393603 / 10000000000000 : ℝ))
      (E := (cell12294 ⟨1, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (8404722777547 / 10000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (230497393603 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_2 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (21003036163111 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576244481147 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨2, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (21003036163111 / 25000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576244481147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_3 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (4198854330779 / 5000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152490960991 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨3, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (4198854330779 / 5000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152490960991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_4 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (10492756703519 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2304985879757 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨4, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (10492756703519 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2304985879757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_5 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (655523794169 / 781250000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (9219959691 / 400000000000 : ℝ))
      (E := (cell12294 ⟨5, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (655523794169 / 781250000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (9219959691 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_6 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (262100195799 / 312500000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576248471549 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨6, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (262100195799 / 312500000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576248471549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_7 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (1676742091963 / 2000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2304997894443 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨7, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (1676742091963 / 2000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2304997894443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_8 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83802171445087 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (144062618619 / 6250000000000 : ℝ))
      (E := (cell12294 ⟨8, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83802171445087 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (144062618619 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_9 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83767263160723 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152502923323 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨9, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83767263160723 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152502923323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_10 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41866189854739 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152504932197 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨10, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41866189854739 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152504932197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_11 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83697521055961 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305013842701 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨11, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83697521055961 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305013842701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_12 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (41831343582481 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461003569367 / 20000000000000 : ℝ))
      (E := (cell12294 ⟨12, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (41831343582481 / 50000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (461003569367 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_13 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83627878001459 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576255456439 / 25000000000000 : ℝ))
      (E := (cell12294 ⟨13, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83627878001459 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (576255456439 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_14 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83593093530611 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152512922137 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨14, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83593093530611 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152512922137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_15 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83558333717759 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305029850807 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨15, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83558333717759 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305029850807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_16 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (10440449816053 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (288129224179 / 12500000000000 : ℝ))
      (E := (cell12294 ⟨16, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (10440449816053 / 12500000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (288129224179 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_17 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83488887928307 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305037794383 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨17, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83488887928307 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305037794383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_18 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (83454201883289 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152520900633 / 50000000000000 : ℝ))
      (E := (cell12294 ⟨18, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (83454201883289 / 100000000000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (1152520900633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12294_19 : CellCertificate 12294 (224598148332659 / 2500000000000000 : ℝ) (1708529101298037 / 1000000000000000000 : ℝ) (345395950004733 / 10000000000000000 : ℝ)
    (cell12294 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · norm_num [cell12294]
  · have h := gap_lower (n := 12294) (a := (325857579529 / 390625000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305045819567 / 100000000000000 : ℝ))
      (E := (cell12294 ⟨19, by decide⟩).energy) (xi := (345395950004733 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12294 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12294]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12294])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12294) (a := (325857579529 / 390625000000 : ℝ)) (b := (167614666021 / 100000000000000 : ℝ)) (q := (2305045819567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12294])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12294]

theorem cert12295_0 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (84082319876479 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304826315877 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨0, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (84082319876479 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304826315877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_1 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (84047211966903 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304830302833 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨1, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (84047211966903 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304830302833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_2 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (21003032294983 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152417144879 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨2, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (21003032294983 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152417144879 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_3 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16795414295729 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304838286319 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨3, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16795414295729 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304838286319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_4 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (1049275485329 / 1250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304842301917 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨4, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (1049275485329 / 1250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304842301917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_5 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83907031186427 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304846287809 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨5, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83907031186427 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304846287809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_6 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83872048522629 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304850310717 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨6, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83872048522629 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304850310717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_7 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83837090798781 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576213565851 / 25000000000000 : ℝ))
      (E := (cell12295 ⟨7, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83837090798781 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (576213565851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_8 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (5237634873683 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152429135003 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨8, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (5237634873683 / 6250000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152429135003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_9 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83767250027303 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304862280661 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨9, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83767250027303 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304862280661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_10 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83732366908329 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152433122577 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨10, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83732366908329 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152433122577 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_11 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83697508586613 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304870228977 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨11, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83697508586613 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304870228977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_12 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83662675026949 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152437119707 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨12, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83662675026949 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152437119707 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_13 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41813933097157 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304878225427 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨13, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41813933097157 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304878225427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_14 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (20898270513467 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (144055140739 / 6250000000000 : ℝ))
      (E := (cell12295 ⟨14, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (20898270513467 / 25000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (144055140739 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_15 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41779161285477 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288110776113 / 12500000000000 : ℝ))
      (E := (cell12295 ⟨15, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41779161285477 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (288110776113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_16 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (41761793855547 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152445109549 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨16, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (41761793855547 / 50000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152445109549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_17 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (83488877439989 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460978846057 / 20000000000000 : ℝ))
      (E := (cell12295 ⟨17, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (83488877439989 / 100000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (460978846057 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_18 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16299646821 / 19531250000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304898189999 / 100000000000000 : ℝ))
      (E := (cell12295 ⟨18, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16299646821 / 19531250000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (2304898189999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12295_19 : CellCertificate 12295 (898362857361733 / 10000000000000000 : ℝ) (427097523202713 / 250000000000000000 : ℝ) (345367112620697 / 10000000000000000 : ℝ)
    (cell12295 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · norm_num [cell12295]
  · have h := gap_lower (n := 12295) (a := (16683906105549 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152451110039 / 50000000000000 : ℝ))
      (E := (cell12295 ⟨19, by decide⟩).energy) (xi := (345367112620697 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12295 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12295]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12295])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12295) (a := (16683906105549 / 20000000000000 : ℝ)) (b := (33520170501 / 20000000000000 : ℝ)) (q := (1152451110039 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12295])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12295]

theorem cert12296_0 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (84082303734009 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576170698841 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨0, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (84082303734009 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576170698841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_1 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (21011799040231 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152343389989 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨1, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (21011799040231 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152343389989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_2 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (21003028427491 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152345382681 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨2, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (21003028427491 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152345382681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_3 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83977056344213 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304694761179 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨3, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83977056344213 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304694761179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_4 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (20985506006737 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230469877683 / 10000000000000 : ℝ))
      (E := (cell12296 ⟨4, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (20985506006737 / 25000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (230469877683 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_5 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (2097675418041 / 2500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576175690893 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨5, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (2097675418041 / 2500000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576175690893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_6 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (16774406878391 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (288088341277 / 12500000000000 : ℝ))
      (E := (cell12296 ⟨6, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (16774406878391 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (288088341277 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_7 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41918538500873 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304710743249 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨7, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41918538500873 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304710743249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_8 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83802144515061 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304714753083 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨8, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83802144515061 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304714753083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_9 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (16753447379227 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152359354891 / 50000000000000 : ℝ))
      (E := (cell12296 ⟨9, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (16753447379227 / 20000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (1152359354891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_10 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83732354109389 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576180684267 / 25000000000000 : ℝ))
      (E := (cell12296 ⟨10, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83732354109389 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (576180684267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_11 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83697496119433 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (72022710203 / 3125000000000 : ℝ))
      (E := (cell12296 ⟨11, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83697496119433 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (72022710203 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_12 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (41831331445531 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304730685277 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨12, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (41831331445531 / 50000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304730685277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_13 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83627854389253 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304734678449 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨13, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83627854389253 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304734678449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_14 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (2612283455599 / 3125000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (288092339099 / 12500000000000 : ℝ))
      (E := (cell12296 ⟨14, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (2612283455599 / 3125000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (288092339099 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_15 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83558311426151 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304742678603 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨15, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83558311426151 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304742678603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_16 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83523576895723 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460949339663 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨16, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83523576895723 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460949339663 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_17 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83488866953589 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304750661637 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨17, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83488866953589 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304750661637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_18 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (8345418156563 / 10000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304754690601 / 100000000000000 : ℝ))
      (E := (cell12296 ⟨18, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (8345418156563 / 10000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (2304754690601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12296_19 : CellCertificate 12296 (179666625210369 / 2000000000000000 : ℝ) (854125553470851 / 500000000000000000 : ℝ) (345338280168627 / 10000000000000000 : ℝ)
    (cell12296 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · norm_num [cell12296]
  · have h := gap_lower (n := 12296) (a := (83419520697903 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460951734867 / 20000000000000 : ℝ))
      (E := (cell12296 ⟨19, by decide⟩).energy) (xi := (345338280168627 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12296 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12296]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12296])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12296) (a := (83419520697903 / 100000000000000 : ℝ)) (b := (167587041293 / 100000000000000 : ℝ)) (q := (460951734867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12296])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12296]

theorem cert12297_0 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (84082287594169 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460907865467 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨0, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (84082287594169 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460907865467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_1 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (84047180357531 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152271683733 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨1, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (84047180357531 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152271683733 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_2 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (84012098242541 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152273675699 / 50000000000000 : ℝ))
      (E := (cell12297 ⟨2, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (84012098242541 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (1152273675699 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_3 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20994260303071 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304551346561 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨3, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20994260303071 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304551346561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_4 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20985502307509 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460911060899 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨4, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20985502307509 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460911060899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_5 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (10488375282409 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304559292153 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨5, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (10488375282409 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304559292153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_6 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (10484002532957 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (144035207401 / 6250000000000 : ℝ))
      (E := (cell12297 ⟨6, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (10484002532957 / 12500000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (144035207401 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_7 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41918531603523 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460913455209 / 20000000000000 : ℝ))
      (E := (cell12297 ⟨7, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41918531603523 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (460913455209 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_8 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83802131053487 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304571289177 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨8, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83802131053487 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304571289177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_9 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83767223767217 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288071913493 / 12500000000000 : ℝ))
      (E := (cell12297 ⟨9, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83767223767217 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (288071913493 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_10 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (41866170656329 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304579282133 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨10, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (41866170656329 / 50000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304579282133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_11 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83697483654421 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304583277231 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨11, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83697483654421 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304583277231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_12 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (836626507573 / 1000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304587242473 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨12, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (836626507573 / 1000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304587242473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_13 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20906960646569 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304591242893 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨13, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20906960646569 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304591242893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_14 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83593059106511 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (92183809087 / 4000000000000 : ℝ))
      (E := (cell12297 ⟨14, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83593059106511 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (92183809087 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_15 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20889575070837 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (9002340859 / 390625000000 : ℝ))
      (E := (cell12297 ⟨15, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20889575070837 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (9002340859 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_16 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83523566082313 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304603231079 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨16, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83523566082313 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304603231079 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_17 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (20872214117277 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (72018975149 / 3125000000000 : ℝ))
      (E := (cell12297 ⟨17, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (20872214117277 / 25000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (72018975149 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_18 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (5215885713101 / 6250000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576152811221 / 25000000000000 : ℝ))
      (E := (cell12297 ⟨18, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (5215885713101 / 6250000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (576152811221 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12297_19 : CellCertificate 12297 (35932135975993 / 400000000000000 : ℝ) (1708112143685067 / 1000000000000000000 : ℝ) (172654726323547 / 5000000000000000 : ℝ)
    (cell12297 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · norm_num [cell12297]
  · have h := gap_lower (n := 12297) (a := (83419510869897 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304615240551 / 100000000000000 : ℝ))
      (E := (cell12297 ⟨19, by decide⟩).energy) (xi := (172654726323547 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12297 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12297]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12297])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12297) (a := (83419510869897 / 100000000000000 : ℝ)) (b := (167573232387 / 100000000000000 : ℝ)) (q := (2304615240551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12297])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12297]

theorem cert12298_0 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (84082271456957 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152197984781 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨0, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (84082271456957 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152197984781 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_1 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (21011791139181 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152199974859 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨1, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (21011791139181 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152199974859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_2 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (42006041388831 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304403932243 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨2, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (42006041388831 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304403932243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_3 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (10497128260357 / 12500000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460881585359 / 20000000000000 : ℝ))
      (E := (cell12298 ⟨3, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (10497128260357 / 12500000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (460881585359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_4 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (81974603941 / 97656250000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304411942777 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨4, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (81974603941 / 97656250000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304411942777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_5 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83906987799321 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304415931441 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨5, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83906987799321 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304415931441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_6 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83872006137733 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152209950799 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨6, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83872006137733 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152209950799 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_7 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83837049414679 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304423919729 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨7, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83837049414679 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304423919729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_8 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (16760423518841 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304427936249 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨8, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (16760423518841 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304427936249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_9 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (20941802660137 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152215950609 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨9, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (20941802660137 / 25000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152215950609 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_10 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (16746465703627 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304435880353 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨10, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (16746465703627 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304435880353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_11 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41848735595787 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304439881189 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨11, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41848735595787 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304439881189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_12 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83662638625663 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152221955503 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨12, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83662638625663 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152221955503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_13 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83627830785383 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230444786069 / 10000000000000 : ℝ))
      (E := (cell12298 ⟨13, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83627830785383 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (230444786069 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_14 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (16718609527179 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152225926537 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨14, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (16718609527179 / 20000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152225926537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_15 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41779144571273 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304455836571 / 100000000000000 : ℝ))
      (E := (cell12298 ⟨15, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41779144571273 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (2304455836571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_16 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83523555270861 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152229937769 / 50000000000000 : ℝ))
      (E := (cell12298 ⟨16, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83523555270861 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (1152229937769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_17 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (5218052874159 / 6250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576115964921 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨17, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (5218052874159 / 6250000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576115964921 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_18 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (83454161255479 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (46089357057 / 2000000000000 : ℝ))
      (E := (cell12298 ⟨18, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (83454161255479 / 100000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (46089357057 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12298_19 : CellCertificate 12298 (449136838702263 / 5000000000000000 : ℝ) (1707973203035429 / 1000000000000000000 : ℝ) (86320157513667 / 2500000000000000 : ℝ)
    (cell12298 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · norm_num [cell12298]
  · have h := gap_lower (n := 12298) (a := (41709750521863 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576117965129 / 25000000000000 : ℝ))
      (E := (cell12298 ⟨19, by decide⟩).energy) (xi := (86320157513667 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12298 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12298]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12298])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12298) (a := (41709750521863 / 50000000000000 : ℝ)) (b := (20944928223 / 12500000000000 : ℝ)) (q := (576117965129 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12298])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12298]

theorem cert12299_0 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (84082255322373 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304252664277 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨0, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (84082255322373 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304252664277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_1 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (84047148758503 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576064160579 / 25000000000000 : ℝ))
      (E := (cell12299 ⟨1, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (84047148758503 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (576064160579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_2 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (42006033657663 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152130340669 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨2, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (42006033657663 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152130340669 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_3 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (10497126369491 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460852935079 / 20000000000000 : ℝ))
      (E := (cell12299 ⟨3, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (10497126369491 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (460852935079 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_4 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83941979643591 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152134316907 / 50000000000000 : ℝ))
      (E := (cell12299 ⟨4, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83941979643591 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (1152134316907 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_5 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83906973341787 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (36004259743 / 1562500000000 : ℝ))
      (E := (cell12299 ⟨5, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83906973341787 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (36004259743 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_6 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41935996007093 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304276653483 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨6, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41935996007093 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304276653483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_7 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (16767407124929 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304280616369 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨7, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (16767407124929 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304280616369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_8 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83802104137213 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304284636343 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨8, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83802104137213 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304284636343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_9 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8376719751613 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304288605557 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨9, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8376719751613 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304288605557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_10 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83732315725819 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (230429258973 / 10000000000000 : ℝ))
      (E := (cell12299 ⟨10, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83732315725819 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (230429258973 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_11 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41848729365447 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288037074549 / 12500000000000 : ℝ))
      (E := (cell12299 ⟨11, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41848729365447 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288037074549 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_12 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83662626496151 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288037571847 / 12500000000000 : ℝ))
      (E := (cell12299 ⟨12, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83662626496151 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288037571847 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_13 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (20906954746643 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304304589913 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨13, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (20906954746643 / 25000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304304589913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_14 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83593036167321 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288038573811 / 12500000000000 : ℝ))
      (E := (cell12299 ⟨14, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83593036167321 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (288038573811 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_15 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (16711655600749 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304312582961 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨15, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (16711655600749 / 20000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304312582961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_16 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (10440443057671 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304316573549 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨16, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (10440443057671 / 12500000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304316573549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_17 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (41744417752949 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304320568217 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨17, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (41744417752949 / 50000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304320568217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_18 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (83454151103219 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (144020285793 / 6250000000000 : ℝ))
      (E := (cell12299 ⟨18, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (83454151103219 / 100000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (144020285793 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

theorem cert12299_19 : CellCertificate 12299 (449121980032401 / 5000000000000000 : ℝ) (213479285623409 / 125000000000000000 : ℝ) (172625906194961 / 5000000000000000 : ℝ)
    (cell12299 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · norm_num [cell12299]
  · have h := gap_lower (n := 12299) (a := (8341949121939 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304328534231 / 100000000000000 : ℝ))
      (E := (cell12299 ⟨19, by decide⟩).energy) (xi := (172625906194961 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12299 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12299]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12299])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12299) (a := (8341949121939 / 10000000000000 : ℝ)) (b := (33509124297 / 20000000000000 : ℝ)) (q := (2304328534231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12299])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12299]

end BstLean.Part263
