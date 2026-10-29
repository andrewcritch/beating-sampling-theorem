import BstLean.Part268CellShard20Checks0

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12850_20 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41689941655891 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116750574197 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨20, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41689941655891 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116750574197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_21 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20836361633857 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233505117729 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨21, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20836361633857 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233505117729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_22 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41655516967003 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223350911593 / 10000000000000 : ℝ))
      (E := (cell12850 ⟨22, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41655516967003 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223350911593 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_23 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83276645474763 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233513146551 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨23, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83276645474763 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233513146551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_24 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (10405285140639 / 12500000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (89340686181 / 4000000000000 : ℝ))
      (E := (cell12850 ⟨24, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (10405285140639 / 12500000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (89340686181 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_25 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41603970426319 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116760571431 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨25, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41603970426319 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116760571431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_26 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41586812312543 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233525172779 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨26, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41586812312543 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233525172779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_27 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83139332410371 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116764594217 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨27, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83139332410371 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116764594217 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_28 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (83105064176569 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (139595824509 / 6250000000000 : ℝ))
      (E := (cell12850 ⟨28, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (83105064176569 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (139595824509 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_29 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (1038385248649 / 1250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116768592997 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨29, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (1038385248649 / 1250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116768592997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_30 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20759149881207 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116770585919 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨30, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20759149881207 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116770585919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_31 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41501201521927 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233545209853 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨31, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41501201521927 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233545209853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_32 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82968230417723 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (55838729609 / 2500000000000 : ℝ))
      (E := (cell12850 ⟨32, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82968230417723 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (55838729609 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_33 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82934081615317 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116776606827 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨33, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82934081615317 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116776606827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_34 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20724989151419 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223355718151 / 10000000000000 : ℝ))
      (E := (cell12850 ⟨34, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20724989151419 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223355718151 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_35 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41432927678999 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233561205867 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨35, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41432927678999 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233561205867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_36 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82831777841637 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116782614311 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨36, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82831777841637 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116782614311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_37 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82797724026103 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558392297839 / 25000000000000 : ℝ))
      (E := (cell12850 ⟨37, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82797724026103 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558392297839 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_38 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41381846940529 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (55839330287 / 2500000000000 : ℝ))
      (E := (cell12850 ⟨38, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41381846940529 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (55839330287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_39 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (258530273051 / 312500000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233577230153 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨39, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (258530273051 / 312500000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233577230153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12851_20 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (20844968684471 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233383080387 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨20, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (20844968684471 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233383080387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_21 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (20836359566781 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233387038099 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨21, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (20836359566781 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233387038099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_22 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83311025970871 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116695541859 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨22, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83311025970871 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116695541859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_23 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83276637816371 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233395045777 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨23, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83276637816371 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233395045777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_24 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (520264211069 / 625000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446679820523 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨24, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (520264211069 / 625000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446679820523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_25 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41603966901231 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233403082153 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨25, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41603966901231 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233403082153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_26 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (5198351117399 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233407103967 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨26, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (5198351117399 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233407103967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_27 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41569662983361 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279176389027 / 12500000000000 : ℝ))
      (E := (cell12851 ⟨27, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41569662983361 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279176389027 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_28 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (2597033063611 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233415109217 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨28, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (2597033063611 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233415109217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_29 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (20767703513279 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558354774263 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨29, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (20767703513279 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558354774263 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_30 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83036593987817 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279177884697 / 12500000000000 : ℝ))
      (E := (cell12851 ⟨30, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83036593987817 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279177884697 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_31 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (83002397808219 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446685422193 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨31, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (83002397808219 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446685422193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_32 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41484112741523 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233431140113 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨32, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41484112741523 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233431140113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_33 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82934076981181 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233435107593 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨33, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82934076981181 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233435107593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_34 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41449976135833 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (3489748643 / 156250000000 : ℝ))
      (E := (cell12851 ⟨34, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41449976135833 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (3489748643 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_35 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82865851323699 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233443154041 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨35, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82865851323699 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233443154041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_36 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (16566354821327 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116723558491 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨36, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (16566354821327 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116723558491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_37 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (2587428768437 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279181392241 / 12500000000000 : ℝ))
      (E := (cell12851 ⟨37, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (2587428768437 / 3125000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (279181392241 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_38 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (8276369074341 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558363789571 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨38, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (8276369074341 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558363789571 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_39 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (8272968453673 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233459177879 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨39, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (8272968453673 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233459177879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12852_20 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (10422483270693 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233265008597 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨20, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (10422483270693 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233265008597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_21 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83345430000341 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233269013041 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨21, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83345430000341 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233269013041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_22 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83311018009219 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233273047799 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨22, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83311018009219 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233273047799 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_23 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41638315079713 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233277058061 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨23, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41638315079713 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233277058061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_24 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83242266418379 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233281047073 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨24, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83242266418379 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233281047073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_25 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83207926753661 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279160627231 / 12500000000000 : ℝ))
      (E := (cell12852 ⟨25, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83207926753661 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (279160627231 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_26 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83173611133021 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233289031597 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨26, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83173611133021 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233289031597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_27 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (133022911239 / 160000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116646516239 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨27, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (133022911239 / 160000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116646516239 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_28 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83105051895801 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233297081287 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨28, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83105051895801 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233297081287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_29 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41535404107771 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233301063167 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨29, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41535404107771 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233301063167 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_30 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (20759147113 / 25000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (69790782451 / 3125000000000 : ℝ))
      (E := (cell12852 ⟨30, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (20759147113 / 25000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (69790782451 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_31 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (83002392573741 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446661813451 / 20000000000000 : ℝ))
      (E := (cell12852 ⟨31, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (83002392573741 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (446661813451 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_32 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (8296822054949 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (223331309253 / 10000000000000 : ℝ))
      (E := (cell12852 ⟨32, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (8296822054949 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (223331309253 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_33 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82934072348131 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233317056829 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨33, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82934072348131 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233317056829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_34 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41449973969353 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233321078267 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨34, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41449973969353 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233321078267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_35 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41432923645207 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233325098989 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨35, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41432923645207 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233325098989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_36 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (8283177037261 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233329119491 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨36, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (8283177037261 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233329119491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_37 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41398858577403 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (44666661627 / 2000000000000 : ℝ))
      (E := (cell12852 ⟨37, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41398858577403 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (44666661627 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_38 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82763687606667 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (89333484079 / 4000000000000 : ℝ))
      (E := (cell12852 ⟨38, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82763687606667 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (89333484079 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_39 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (8272968169801 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116670561263 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨39, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (8272968169801 / 10000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116670561263 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12853_20 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83379857594761 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (55828674783 / 2500000000000 : ℝ))
      (E := (cell12853 ⟨20, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83379857594761 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (55828674783 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_21 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83345421735079 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233150984239 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨21, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83345421735079 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233150984239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_22 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20827752512263 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116577504087 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨22, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20827752512263 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116577504087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_23 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83276622503929 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233159008313 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨23, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83276622503929 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233159008313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_24 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (83242259067129 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (139572690393 / 6250000000000 : ℝ))
      (E := (cell12853 ⟨24, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (83242259067129 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (139572690393 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_25 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41603959853117 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (55829175209 / 2500000000000 : ℝ))
      (E := (cell12853 ⟨25, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41603959853117 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (55829175209 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_26 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20793401097249 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279146376763 / 12500000000000 : ℝ))
      (E := (cell12853 ⟨26, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20793401097249 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279146376763 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_27 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (8313931308333 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116587503839 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨27, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (8313931308333 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116587503839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_28 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20776261439329 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116589524937 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨28, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20776261439329 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116589524937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_29 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20767700594799 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233183025839 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨29, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20767700594799 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233183025839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_30 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (324361652021 / 390625000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279148381801 / 12500000000000 : ℝ))
      (E := (cell12853 ⟨30, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (324361652021 / 390625000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279148381801 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_31 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (4150119367021 / 5000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116595539363 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨31, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (4150119367021 / 5000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116595539363 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_32 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16593643123411 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446639008323 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨32, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16593643123411 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446639008323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_33 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16586813543233 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279149882671 / 12500000000000 : ℝ))
      (E := (cell12853 ⟨33, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16586813543233 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (279149882671 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_34 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41449971803397 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233203080377 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨34, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41449971803397 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233203080377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_35 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (82865843258141 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233207099361 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨35, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (82865843258141 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233207099361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_36 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41415883319781 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116605530073 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨36, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41415883319781 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116605530073 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_37 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (8279771372057 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233215080313 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨37, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (8279771372057 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233215080313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_38 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (8276368447083 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233219101267 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨38, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (8276368447083 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233219101267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_39 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (129265123219 / 156250000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446644624567 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨39, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (129265123219 / 156250000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446644624567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12854_20 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (16675969805107 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116514514277 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨20, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (16675969805107 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116514514277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_21 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83345413471337 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (223303301001 / 10000000000000 : ℝ))
      (E := (cell12854 ⟨21, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83345413471337 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (223303301001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_22 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (650867203831 / 781250000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233037023183 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨22, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (650867203831 / 781250000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233037023183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_23 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83276614849879 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (111652050663 / 5000000000000 : ℝ))
      (E := (cell12854 ⟨23, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83276614849879 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (111652050663 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_24 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83242251717289 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233045041871 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨24, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83242251717289 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233045041871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_25 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (83207912660181 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233049053689 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨25, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (83207912660181 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233049053689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_26 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (20793399411577 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233053051489 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨26, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (20793399411577 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233053051489 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_27 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41569653321793 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446611407563 / 20000000000000 : ℝ))
      (E := (cell12854 ⟨27, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41569653321793 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446611407563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_28 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (40578632627 / 48828125000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233061073459 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨28, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (40578632627 / 48828125000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233061073459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_29 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (1038384956801 / 1250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139566565223 / 6250000000000 : ℝ))
      (E := (cell12854 ⟨29, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (1038384956801 / 1250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139566565223 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_30 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (10379572172993 / 12500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (69783408343 / 3125000000000 : ℝ))
      (E := (cell12854 ⟨30, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (10379572172993 / 12500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (69783408343 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_31 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (2593824440883 / 3125000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89322923473 / 4000000000000 : ℝ))
      (E := (cell12854 ⟨31, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (2593824440883 / 3125000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89322923473 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_32 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82968210685741 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116538522969 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨32, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82968210685741 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116538522969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_33 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (20733515771321 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139567566413 / 6250000000000 : ℝ))
      (E := (cell12854 ⟨33, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (20733515771321 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139567566413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_34 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82899939275931 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89323403169 / 4000000000000 : ℝ))
      (E := (cell12854 ⟨34, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82899939275931 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (89323403169 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_35 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82865839226881 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558272274127 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨35, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82865839226881 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558272274127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_36 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82831762907491 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233093114949 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨36, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82831762907491 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233093114949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_37 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (3311908411491 / 4000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (17864776609 / 800000000000 : ℝ))
      (E := (cell12854 ⟨37, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (3311908411491 / 4000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (17864776609 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_38 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41381840667949 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446620219489 / 20000000000000 : ℝ))
      (E := (cell12854 ⟨38, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41381840667949 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446620219489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_39 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (4136483801159 / 5000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116552560033 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨39, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (4136483801159 / 5000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116552560033 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12855_20 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16675968091573 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232911062011 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨20, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16675968091573 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232911062011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_21 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41672702604557 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116457545179 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨21, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41672702604557 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116457545179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_22 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83310994133167 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232919092829 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨22, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83310994133167 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232919092829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_23 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (20819151799319 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (279115384113 / 12500000000000 : ℝ))
      (E := (cell12855 ⟨23, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (20819151799319 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (279115384113 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_24 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83242244368859 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232927092213 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨24, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83242244368859 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232927092213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_25 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41603952807751 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232931095427 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨25, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41603952807751 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232931095427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_26 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41586795452479 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232935085319 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨26, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41586795452479 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232935085319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_27 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (83139300205143 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558234766109 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨27, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (83139300205143 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558234766109 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_28 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (4155251674207 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116471546783 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨28, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (4155251674207 / 5000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116471546783 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_29 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (5191924419387 / 6250000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232947116359 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨29, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (5191924419387 / 6250000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232947116359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_30 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16607314370341 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116475538069 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨30, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16607314370341 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116475538069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_31 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (1296912138707 / 1562500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558238772889 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨31, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (1296912138707 / 1562500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558238772889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_32 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41484102877773 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446591821101 / 20000000000000 : ℝ))
      (E := (cell12855 ⟨32, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41484102877773 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446591821101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_33 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82934058455487 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (139560194947 / 6250000000000 : ℝ))
      (E := (cell12855 ⟨33, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82934058455487 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (139560194947 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_34 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (20724983736529 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232967133437 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨34, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (20724983736529 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232967133437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_35 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82865835196633 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116485574539 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨35, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82865835196633 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116485574539 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_36 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82831759176397 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232975166567 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨36, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82831759176397 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232975166567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_37 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (2069942671373 / 2500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116489563741 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨37, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (2069942671373 / 2500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116489563741 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_38 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82763678201871 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232983149227 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨38, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82763678201871 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232983149227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_39 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82729673187069 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232987172961 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨39, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82729673187069 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2232987172961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12856_20 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83379831891751 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232793149981 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨20, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83379831891751 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232793149981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_21 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83345396948411 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116398554323 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨21, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83345396948411 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116398554323 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_22 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83310986177449 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232801158771 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨22, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83310986177449 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232801158771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_23 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41638299773059 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116402564441 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨23, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41638299773059 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116402564441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_24 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41621118510919 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116404569463 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨24, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41621118510919 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116404569463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_25 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20801974643049 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558203283393 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨25, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20801974643049 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558203283393 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_26 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (5198349010309 / 6250000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232817174029 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨26, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (5198349010309 / 6250000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232817174029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_27 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (83139293768001 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446564229199 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨27, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (83139293768001 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446564229199 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_28 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (10388128418681 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232825168673 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨28, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (10388128418681 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232825168673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_29 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20767696219383 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232829185707 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨29, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20767696219383 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232829185707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_30 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41518283160329 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232833198949 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨30, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41518283160329 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232833198949 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_31 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (16600474329479 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232837151469 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨31, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (16600474329479 / 20000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232837151469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_32 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (10371025103309 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232841161739 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨32, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (10371025103309 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232841161739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_33 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41467026913387 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (5582112931 / 250000000000 : ℝ))
      (E := (cell12856 ⟨33, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41467026913387 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (5582112931 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_34 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82899930617349 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223284918439 / 10000000000000 : ℝ))
      (E := (cell12856 ⟨34, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82899930617349 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223284918439 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_35 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82865831167397 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232853198427 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨35, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82865831167397 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232853198427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_36 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41415877723139 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232857215001 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨36, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41415877723139 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232857215001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_37 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41398851711753 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232861234381 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨37, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41398851711753 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232861234381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_38 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20690918767187 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232865197897 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨38, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20690918767187 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232865197897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_39 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82729670351827 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232869222781 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨39, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82729670351827 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232869222781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12857_20 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83379823327193 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89307009367 / 4000000000000 : ℝ))
      (E := (cell12857 ⟨20, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83379823327193 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89307009367 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_21 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41672694344613 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232679239831 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨21, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41672694344613 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232679239831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_22 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83310978223213 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232683221011 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨22, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83310978223213 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232683221011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_23 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83276591896407 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116343619779 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨23, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83276591896407 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116343619779 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_24 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83242229676227 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232691240399 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨24, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83242229676227 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232691240399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_25 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83207891530263 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232695226539 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨25, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83207891530263 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232695226539 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_26 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83173577426267 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232699259187 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨26, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83173577426267 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232699259187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_27 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83139287332159 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116351641249 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨27, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83139287332159 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116351641249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_28 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83105021216021 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116353620151 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨28, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83105021216021 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116353620151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_29 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (83070779046099 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446542250323 / 20000000000000 : ℝ))
      (E := (cell12857 ⟨29, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (83070779046099 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446542250323 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_30 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41518280395401 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232715259829 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨30, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41518280395401 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232715259829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_31 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41501183209349 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116359633283 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨31, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41501183209349 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116359633283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_32 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20742048974629 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232723273219 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨32, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20742048974629 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232723273219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_33 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (16586809839829 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232727280953 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨33, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (16586809839829 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232727280953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_34 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82899926289629 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232731290709 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨34, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82899926289629 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232731290709 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_35 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82865827139173 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232735303201 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨35, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82865827139173 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232735303201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_36 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (5176984482321 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (55818482973 / 2500000000000 : ℝ))
      (E := (cell12857 ⟨36, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (5176984482321 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (55818482973 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_37 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (10349712499129 / 12500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116371669067 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨37, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (10349712499129 / 12500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116371669067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_38 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82763671936531 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558186825543 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨38, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82763671936531 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558186825543 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_39 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41364833758727 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116375664133 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨39, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41364833758727 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116375664133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12858_20 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83379814764189 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232557372887 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨20, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83379814764189 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232557372887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_21 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (2083634510789 / 2500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558140341819 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨21, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (2083634510789 / 2500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558140341819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_22 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83310970270459 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232565337891 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨22, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83310970270459 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232565337891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_23 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83276584248141 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232569346571 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨23, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83276584248141 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232569346571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_24 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (3329688893281 / 4000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446514667649 / 20000000000000 : ℝ))
      (E := (cell12858 ⟨24, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (3329688893281 / 4000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446514667649 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_25 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41603942244851 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232577374327 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨25, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41603942244851 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232577374327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_26 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41586785344463 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232581399227 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨26, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41586785344463 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232581399227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_27 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83139280897617 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558146339257 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨27, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83139280897617 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558146339257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_28 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83105015083857 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116294683467 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨28, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83105015083857 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116294683467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_29 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (16614154643179 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446518674517 / 20000000000000 : ℝ))
      (E := (cell12858 ⟨29, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (16614154643179 / 20000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446518674517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_30 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41518277631069 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232597375833 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨30, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41518277631069 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232597375833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_31 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (83002361191157 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279075172287 / 12500000000000 : ℝ))
      (E := (cell12858 ⟨31, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (83002361191157 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279075172287 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_32 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82968190971681 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232605381367 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨32, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82968190971681 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232605381367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_33 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41467022286299 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232609386213 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨33, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41467022286299 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232609386213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_34 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82899921962957 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232613393771 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨34, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82899921962957 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232613393771 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_35 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82865823111961 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446523480951 / 20000000000000 : ℝ))
      (E := (cell12858 ⟨35, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82865823111961 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (446523480951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_36 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82831747988969 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279077677457 / 12500000000000 : ℝ))
      (E := (cell12858 ⟨36, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82831747988969 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279077677457 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_37 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41398848281749 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232625438741 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨37, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41398848281749 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232625438741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_38 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82763668805217 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116314731027 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨38, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82763668805217 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116314731027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_39 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82729664683949 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116316715339 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨39, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82729664683949 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116316715339 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12859_20 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83379806202741 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232439507823 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨20, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83379806202741 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232439507823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_21 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20836343043853 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232443490983 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨21, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20836343043853 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232443490983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_22 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83310962319187 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223244750941 / 10000000000000 : ℝ))
      (E := (cell12859 ⟨22, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83310962319187 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223244750941 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_23 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83276576601319 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232451508287 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨23, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83276576601319 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232451508287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_24 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (5202638436827 / 6250000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232455490853 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨24, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (5202638436827 / 6250000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232455490853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_25 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41603938725257 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232459518527 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨25, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41603938725257 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232459518527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_26 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83173563952921 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558115883929 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨26, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83173563952921 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558115883929 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_27 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41569637232187 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232467544961 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨27, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41569637232187 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232467544961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_28 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83105008952957 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223247154857 / 10000000000000 : ℝ))
      (E := (cell12859 ⟨28, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83105008952957 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (223247154857 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_29 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (83070767386917 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232475548621 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨29, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (83070767386917 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232475548621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_30 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (16607309946933 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116239773481 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨30, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (16607309946933 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116239773481 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_31 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (8300235596477 / 10000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558120886303 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨31, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (8300235596477 / 10000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558120886303 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_32 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20742046511491 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232487544763 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨32, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20742046511491 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232487544763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_33 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (16586807989427 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232491546779 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨33, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (16586807989427 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232491546779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_34 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20724979409333 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232495552199 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨34, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20724979409333 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232495552199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_35 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82865819085759 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (279062445217 / 12500000000000 : ℝ))
      (E := (cell12859 ⟨35, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82865819085759 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (279062445217 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_36 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41415872130889 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232503575879 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨36, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41415872130889 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232503575879 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_37 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (10349711641863 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116253797447 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨37, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (10349711641863 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116253797447 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_38 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82763665674807 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232511618827 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨38, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82763665674807 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232511618827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_39 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82729661851313 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558128897189 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨39, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82729661851313 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558128897189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12860_20 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41689898821423 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232321697279 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨20, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41689898821423 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232321697279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_21 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41672681960391 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223232566927 / 10000000000000 : ℝ))
      (E := (cell12860 ⟨21, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41672681960391 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223232566927 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_22 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20827738592349 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223232967723 / 10000000000000 : ℝ))
      (E := (cell12860 ⟨22, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20827738592349 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223232967723 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_23 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83276568955943 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232333666339 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨23, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83276568955943 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232333666339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_24 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83242207647847 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232337698223 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨24, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83242207647847 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232337698223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_25 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41603935206349 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232341717549 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨25, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41603935206349 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232341717549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_26 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20793389304563 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (139521607943 / 6250000000000 : ℝ))
      (E := (cell12860 ⟨26, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20793389304563 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (139521607943 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_27 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83139268032431 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232349729379 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨27, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83139268032431 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232349729379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_28 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83105002823319 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223235372673 / 10000000000000 : ℝ))
      (E := (cell12860 ⟨28, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83105002823319 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223235372673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_29 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (83070761559167 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232357721217 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨29, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (83070761559167 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232357721217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_30 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41518272104191 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232361714689 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨30, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41518272104191 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232361714689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_31 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41501175369769 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232365708763 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨31, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41501175369769 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232365708763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_32 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41484090560683 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558092440851 / 25000000000000 : ℝ))
      (E := (cell12860 ⟨32, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41484090560683 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558092440851 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_33 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (16586807064551 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558093440663 / 25000000000000 : ℝ))
      (E := (cell12860 ⟨33, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (16586807064551 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558093440663 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_34 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41449956656377 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116188882997 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨34, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41449956656377 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116188882997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_35 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82865815060569 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34880965221 / 1562500000000 : ℝ))
      (E := (cell12860 ⟨35, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82865815060569 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34880965221 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_36 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41415870267781 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232385787589 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨36, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41415870267781 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232385787589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_37 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82797689707249 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232389747903 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨37, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82797689707249 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232389747903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_38 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82763662545301 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232393772491 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨38, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82763662545301 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232393772491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_39 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (10341207377443 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232397802503 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨39, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (10341207377443 / 12500000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232397802503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12861_20 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41689894542253 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232203882961 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨20, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41689894542253 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232203882961 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_21 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83345355667669 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (111610395107 / 5000000000000 : ℝ))
      (E := (cell12861 ⟨21, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83345355667669 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (111610395107 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_22 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16662189284217 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232211899693 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨22, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16662189284217 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232211899693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_23 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83276561312011 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116107939547 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨23, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83276561312011 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116107939547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_24 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (8324220030787 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (223221990197 / 10000000000000 : ℝ))
      (E := (cell12861 ⟨24, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (8324220030787 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (223221990197 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_25 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83207863376253 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116111956493 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨25, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83207863376253 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116111956493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_26 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41586775242459 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (69757122341 / 3125000000000 : ℝ))
      (E := (cell12861 ⟨26, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41586775242459 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (69757122341 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_27 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41569630800893 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116115955143 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨27, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41569630800893 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116115955143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_28 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16620999338989 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446447180283 / 20000000000000 : ℝ))
      (E := (cell12861 ⟨28, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16620999338989 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446447180283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_29 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41535377866321 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232239948881 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨29, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41535377866321 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232239948881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_30 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (8303653868329 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279030492193 / 12500000000000 : ℝ))
      (E := (cell12861 ⟨30, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (8303653868329 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279030492193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_31 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (83002345515461 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232247927501 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨31, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (83002345515461 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232247927501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_32 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41484088098943 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139515745009 / 6250000000000 : ℝ))
      (E := (cell12861 ⟨32, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41484088098943 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (139515745009 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_33 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (1295844229679 / 1562500000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558063993809 / 25000000000000 : ℝ))
      (E := (cell12861 ⟨33, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (1295844229679 / 1562500000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558063993809 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_34 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41449954494611 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232259976537 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨34, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41449954494611 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232259976537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_35 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82865811036389 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279032997917 / 12500000000000 : ℝ))
      (E := (cell12861 ⟨35, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82865811036389 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (279032997917 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_36 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (1035396710129 / 1250000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (55806699903 / 2500000000000 : ℝ))
      (E := (cell12861 ⟨36, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (1035396710129 / 1250000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (55806699903 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_37 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82797686280533 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232271956461 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨37, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82797686280533 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232271956461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_38 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82763659416699 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232275981763 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨38, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82763659416699 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232275981763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_39 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (20682414047161 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116140006589 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨39, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (20682414047161 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116140006589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12862_20 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83379780527719 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446417224633 / 20000000000000 : ℝ))
      (E := (cell12862 ⟨20, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83379780527719 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446417224633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_21 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83345347416073 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116045065637 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨21, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83345347416073 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116045065637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_22 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (5206933654641 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232094118457 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨22, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (5206933654641 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232094118457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_23 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83276553669523 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232098146553 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨23, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83276553669523 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232098146553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_24 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (832421929693 / 1000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232102160483 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨24, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (832421929693 / 1000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232102160483 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_25 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83207856341179 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232106163249 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨25, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83207856341179 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232106163249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_26 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41586771876459 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116055078811 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨26, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41586771876459 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116055078811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_27 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (2078481379311 / 2500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (111605707307 / 5000000000000 : ℝ))
      (E := (cell12862 ⟨27, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (2078481379311 / 2500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (111605707307 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_28 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (10388123820979 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558029532777 / 25000000000000 : ℝ))
      (E := (cell12862 ⟨28, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (10388123820979 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558029532777 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_29 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (5191921869209 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558030543277 / 25000000000000 : ℝ))
      (E := (cell12862 ⟨29, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (5191921869209 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558030543277 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_30 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20759133289847 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116063078499 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨30, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20759133289847 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116063078499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_31 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (83002340292537 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558032550357 / 25000000000000 : ℝ))
      (E := (cell12862 ⟨31, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (83002340292537 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558032550357 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_32 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20742042818881 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558033547677 / 25000000000000 : ℝ))
      (E := (cell12862 ⟨32, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20742042818881 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (558033547677 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_33 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (2073350651931 / 2500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232138184529 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨33, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (2073350651931 / 2500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232138184529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_34 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82899904666737 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116071091913 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨34, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82899904666737 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116071091913 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_35 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (4143290350661 / 5000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232146189311 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨35, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (4143290350661 / 5000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232146189311 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_36 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82831733086053 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232150201471 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨36, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82831733086053 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232150201471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_37 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (20699420713689 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279019277571 / 12500000000000 : ℝ))
      (E := (cell12862 ⟨37, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (20699420713689 / 25000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279019277571 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_38 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82763656288999 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232158187931 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨38, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82763656288999 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232158187931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_39 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82729653358611 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (139510138799 / 6250000000000 : ℝ))
      (E := (cell12862 ⟨39, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82729653358611 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (139510138799 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12863_20 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41689885986243 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231968359597 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨20, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41689885986243 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231968359597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_21 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41672669582997 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115986178337 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨21, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41672669582997 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115986178337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_22 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41655465264453 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231976391867 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨22, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41655465264453 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231976391867 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_23 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41638273014239 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115990205177 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨23, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41638273014239 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1115990205177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_24 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41621092816069 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (557996103843 / 25000000000000 : ℝ))
      (E := (cell12863 ⟨24, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41621092816069 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (557996103843 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_25 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (20801962326869 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231988409927 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨25, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (20801962326869 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2231988409927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_26 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83173537022253 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139499524799 / 6250000000000 : ℝ))
      (E := (cell12863 ⟨26, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83173537022253 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139499524799 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_27 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83139248744393 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (111599821847 / 5000000000000 : ℝ))
      (E := (cell12863 ⟨27, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83139248744393 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (111599821847 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_28 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41552492220991 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232000415809 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨28, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41552492220991 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232000415809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_29 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (10383843010409 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232004452403 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨29, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (10383843010409 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232004452403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_30 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (20759131909169 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232008431581 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨30, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (20759131909169 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232008431581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_31 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (83002335070767 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232012413441 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨31, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (83002335070767 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232012413441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_32 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (2074204158857 / 2500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232016457947 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨32, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (2074204158857 / 2500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232016457947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_33 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41467010728053 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232020449133 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨33, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41467010728053 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232020449133 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_34 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82899900345297 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116012223243 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨34, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82899900345297 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116012223243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_35 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (4143290149553 / 5000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232028450717 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨35, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (4143290149553 / 5000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232028450717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_36 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82831729362761 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (279004057789 / 12500000000000 : ℝ))
      (E := (cell12863 ⟨36, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82831729362761 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (279004057789 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_37 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82797679429917 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116018240767 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨37, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82797679429917 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116018240767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_38 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82763653162203 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232040449707 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨38, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82763653162203 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232040449707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_39 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16545930105889 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (111602224203 / 5000000000000 : ℝ))
      (E := (cell12863 ⟨39, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16545930105889 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (111602224203 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12864_20 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16675952683761 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231850650553 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨20, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16675952683761 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231850650553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_21 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83345330917431 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231854694977 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨21, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83345330917431 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231854694977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_22 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20827730646259 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (111592933079 / 5000000000000 : ℝ))
      (E := (cell12864 ⟨22, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20827730646259 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (111592933079 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_23 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83276538388877 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (69745708453 / 3125000000000 : ℝ))
      (E := (cell12864 ⟨23, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83276538388877 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (69745708453 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_24 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41621089148191 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115933333321 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨24, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41621089148191 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115933333321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_25 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (10400980284393 / 12500000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231870711431 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨25, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (10400980284393 / 12500000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231870711431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_26 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83173530292923 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115937345417 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨26, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83173530292923 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115937345417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_27 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83139242317643 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278984840529 / 12500000000000 : ℝ))
      (E := (cell12864 ⟨27, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83139242317643 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278984840529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_28 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83104978317393 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115941348519 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨28, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83104978317393 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115941348519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_29 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41535369130213 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115943364131 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨29, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41535369130213 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115943364131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_30 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83036522115153 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115945351383 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨30, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83036522115153 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115945351383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_31 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (83002329850151 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557973684799 / 25000000000000 : ℝ))
      (E := (cell12864 ⟨31, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (83002329850151 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557973684799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_32 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82968161434153 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231898721861 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨32, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82968161434153 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231898721861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_33 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82934016836053 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231902710449 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨33, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82934016836053 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231902710449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_34 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82899896024903 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231906764517 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨34, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82899896024903 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231906764517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_35 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82865798969911 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115955383777 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨35, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82865798969911 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115955383777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_36 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41415862820221 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446382955729 / 20000000000000 : ℝ))
      (E := (cell12864 ⟨36, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41415862820221 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446382955729 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_37 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82797676006017 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115959369679 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨37, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82797676006017 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115959369679 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_38 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82763650036309 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278990345887 / 12500000000000 : ℝ))
      (E := (cell12864 ⟨38, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82763650036309 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278990345887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_39 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41364823850573 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557981686067 / 25000000000000 : ℝ))
      (E := (cell12864 ⟨39, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41364823850573 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557981686067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12865_20 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83379754866677 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115866498017 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨20, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83379754866677 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115866498017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_21 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (5209082666899 / 6250000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223173697123 / 10000000000000 : ℝ))
      (E := (cell12865 ⟨21, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (5209082666899 / 6250000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223173697123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_22 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (16662182928529 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231740985941 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨22, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (16662182928529 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231740985941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_23 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83276530750719 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115872492673 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨23, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83276530750719 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115872492673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_24 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83242170962033 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231749031067 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨24, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83242170962033 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231749031067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_25 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83207835244181 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446350601871 / 20000000000000 : ℝ))
      (E := (cell12865 ⟨25, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83207835244181 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446350601871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_26 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41586761782463 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115878519887 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨26, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41586761782463 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115878519887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_27 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (83139235892191 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139485063001 / 6250000000000 : ℝ))
      (E := (cell12865 ⟨27, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (83139235892191 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (139485063001 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_28 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41552486097033 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231765033277 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨28, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41552486097033 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231765033277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_29 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20767683109701 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231769000689 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨29, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20767683109701 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231769000689 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_30 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (4151825829741 / 5000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115886514541 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨30, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (4151825829741 / 5000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115886514541 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_31 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (2593822644709 / 3125000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231777061591 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨31, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (2593822644709 / 3125000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231777061591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_32 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82968156515143 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231781041027 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨32, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82968156515143 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231781041027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_33 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82934012217081 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231785027077 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨33, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82934012217081 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231785027077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_34 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41449945852777 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115894539649 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨34, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41449945852777 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115894539649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_35 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82865794949771 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115896540589 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨35, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82865794949771 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115896540589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_36 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82831721919097 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231797091801 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨36, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82831721919097 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231797091801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_37 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (16559534516611 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446360210547 / 20000000000000 : ℝ))
      (E := (cell12865 ⟨37, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (16559534516611 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446360210547 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_38 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82763646911317 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115902540691 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨38, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82763646911317 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115902540691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_39 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41364822436857 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231809060149 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨39, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41364822436857 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231809060149 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12866_20 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (833797463161 / 1000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557903834437 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨20, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (833797463161 / 1000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557903834437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_21 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20836328606213 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557904840097 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨21, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20836328606213 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557904840097 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_22 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83310906701733 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (44632467299 / 2000000000000 : ℝ))
      (E := (cell12866 ⟨22, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83310906701733 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (44632467299 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_23 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83276523114003 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446325470981 / 20000000000000 : ℝ))
      (E := (cell12866 ⟨23, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83276523114003 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446325470981 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_24 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83242163629089 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231631333487 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨24, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83242163629089 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231631333487 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_25 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83207828214589 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557908840527 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨25, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83207828214589 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557908840527 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_26 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41586758419131 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231639385171 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨26, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41586758419131 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231639385171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_27 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20784807367009 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231643346751 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨27, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20784807367009 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231643346751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_28 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (10388120759 / 12500000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115823683023 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨28, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (10388120759 / 12500000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115823683023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_29 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (10383840827301 / 12500000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557912846673 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨29, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (10383840827301 / 12500000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557912846673 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_30 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (3321460443027 / 4000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231655352003 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨30, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (3321460443027 / 4000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231655352003 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_31 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (83002319412377 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557914845157 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨31, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (83002319412377 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557914845157 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_32 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (82968151597251 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115831707723 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨32, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (82968151597251 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115831707723 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_33 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (82934007599191 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115833699509 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨33, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (82934007599191 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115833699509 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_34 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (331599549549 / 400000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231671390831 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨34, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (331599549549 / 400000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231671390831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_35 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (1035822386633 / 1250000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (223167539159 / 10000000000000 : ℝ))
      (E := (cell12866 ⟨35, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (1035822386633 / 1250000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (223167539159 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_36 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41415859099363 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115839700891 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨36, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41415859099363 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115839700891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_37 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (8279766916103 / 10000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115841710833 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨37, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (8279766916103 / 10000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115841710833 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_38 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20690910946807 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (27896093141 / 1250000000000 : ℝ))
      (E := (cell12866 ⟨38, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20690910946807 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (27896093141 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_39 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20682410511787 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (278961428963 / 12500000000000 : ℝ))
      (E := (cell12866 ⟨39, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20682410511787 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (278961428963 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12867_20 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20844934441769 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231497675693 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨20, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20844934441769 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231497675693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_21 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20836326545209 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115750843749 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨21, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20836326545209 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115750843749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_22 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (833108987623 / 1000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (89260227277 / 4000000000000 : ℝ))
      (E := (cell12867 ⟨22, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (833108987623 / 1000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (89260227277 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_23 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83276515478729 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278938715101 / 12500000000000 : ℝ))
      (E := (cell12867 ⟨23, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83276515478729 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278938715101 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_24 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (5202634768597 / 6250000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (89260547627 / 4000000000000 : ℝ))
      (E := (cell12867 ⟨24, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (5202634768597 / 6250000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (89260547627 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_25 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41603910593183 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231517711279 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨25, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41603910593183 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231517711279 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_26 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20793377528233 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115760863511 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨26, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20793377528233 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115760863511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_27 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41569611522589 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231525740437 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨27, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41569611522589 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231525740437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_28 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41552479975597 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557882438457 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨28, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41552479975597 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557882438457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_29 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20767680199809 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115766884631 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨29, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20767680199809 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115766884631 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_30 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83036505557719 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278942216257 / 12500000000000 : ℝ))
      (E := (cell12867 ⟨30, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83036505557719 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278942216257 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_31 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (83002314195219 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231541754857 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨31, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (83002314195219 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231541754857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_32 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41484073340237 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231545786543 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨32, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41484073340237 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231545786543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_33 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82934002982381 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115774883837 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨33, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82934002982381 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115774883837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_34 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10362485383749 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278944219717 / 12500000000000 : ℝ))
      (E := (cell12867 ⟨34, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10362485383749 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278944219717 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_35 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (41432893456259 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557889439359 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨35, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (41432893456259 / 50000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557889439359 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_36 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (2588491077479 / 3125000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278945220907 / 12500000000000 : ℝ))
      (E := (cell12867 ⟨36, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (2588491077479 / 3125000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (278945220907 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_37 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82797665739943 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115782893729 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨37, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82797665739943 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115782893729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_38 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (2069091016601 / 2500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231569818077 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨38, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (2069091016601 / 2500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231569818077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_39 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82729639221449 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (8717085157 / 390625000000 : ℝ))
      (E := (cell12867 ⟨39, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82729639221449 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (8717085157 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12868_20 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41689864609801 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231380126461 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨20, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41689864609801 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231380126461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_21 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41672648969167 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115692063757 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨21, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41672648969167 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115692063757 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_22 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (16662178164869 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223138811189 / 10000000000000 : ℝ))
      (E := (cell12868 ⟨22, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (16662178164869 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223138811189 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_23 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83276507844897 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231392141421 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨23, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83276507844897 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231392141421 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_24 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (4162107448371 / 5000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446279220527 / 20000000000000 : ℝ))
      (E := (cell12868 ⟨24, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (4162107448371 / 5000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446279220527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_25 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (10400976769939 / 12500000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231400115283 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨25, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (10400976769939 / 12500000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231400115283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_26 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41586751694467 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231404123767 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨26, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41586751694467 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231404123767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_27 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (40595320617 / 48828125000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231408130619 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨27, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (40595320617 / 48828125000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231408130619 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_28 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83104953831649 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (111570606907 / 5000000000000 : ℝ))
      (E := (cell12868 ⟨28, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83104953831649 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (111570606907 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_29 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83070714981289 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231416148401 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨29, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83070714981289 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231416148401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_30 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83036500040951 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231420163243 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨30, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83036500040951 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231420163243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_31 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (83002308979213 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (69732003929 / 3125000000000 : ℝ))
      (E := (cell12868 ⟨31, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (83002308979213 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (69732003929 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_32 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41484070882407 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231428154319 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨32, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41484070882407 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231428154319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_33 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82933998366651 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446286438329 / 20000000000000 : ℝ))
      (E := (cell12868 ⟨33, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82933998366651 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446286438329 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_34 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82899878753777 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115718090009 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨34, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82899878753777 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115718090009 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_35 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (16573156579081 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231440178717 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨35, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (16573156579081 / 20000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231440178717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_36 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82831710760903 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115722094113 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨36, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82831710760903 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115722094113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_37 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41398831159897 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557862052201 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨37, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41398831159897 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557862052201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_38 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41381818770877 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231452181773 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨38, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41381818770877 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231452181773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_39 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (10341204549577 / 12500000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446291244871 / 20000000000000 : ℝ))
      (E := (cell12868 ⟨39, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (10341204549577 / 12500000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446291244871 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12869_20 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (1042246508421 / 1250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (69726953599 / 3125000000000 : ℝ))
      (E := (cell12869 ⟨20, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (1042246508421 / 1250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (69726953599 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_21 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41672644848673 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446253301097 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨21, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41672644848673 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446253301097 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_22 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83310882887867 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446254107633 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨22, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83310882887867 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446254107633 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_23 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41638250106253 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231274558381 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨23, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41638250106253 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231274558381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_24 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83242141638693 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231278569367 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨24, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83242141638693 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231278569367 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_25 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41603903567013 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (55782064353 / 2500000000000 : ℝ))
      (E := (cell12869 ⟨25, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41603903567013 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (55782064353 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_26 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83173496666269 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446257315081 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨26, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83173496666269 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446257315081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_27 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83139210203351 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231290575753 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨27, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83139210203351 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231290575753 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_28 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (20776236928341 / 25000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231294577467 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨28, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (20776236928341 / 25000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231294577467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_29 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16614141832913 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446259716523 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨29, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16614141832913 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446259716523 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_30 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8303649452537 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115651296519 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨30, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8303649452537 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115651296519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_31 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (83002303764359 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446261310359 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨31, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (83002303764359 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446261310359 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_32 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8296813685027 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231310577351 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨32, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8296813685027 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231310577351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_33 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82933993752001 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115657306167 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨33, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82933993752001 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115657306167 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_34 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82899874438607 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557829649763 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨34, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82899874438607 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557829649763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_35 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (828657788793 / 1000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557830649197 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨35, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (828657788793 / 1000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557830649197 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_36 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (1656634140869 / 2000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231326606023 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨36, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (1656634140869 / 2000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231326606023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_37 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82797658900581 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115665313507 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨37, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82797658900581 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115665313507 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_38 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8276363442037 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231334601083 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨38, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8276363442037 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231334601083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_39 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82729633572649 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115669322727 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨39, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82729633572649 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115669322727 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12870_20 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20844928032327 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231144958407 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨20, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20844928032327 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231144958407 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_21 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83345281457873 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446229799273 / 20000000000000 : ℝ))
      (E := (cell12870 ⟨21, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83345281457873 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446229799273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_22 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20827718738217 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (8924611843 / 400000000000 : ℝ))
      (E := (cell12870 ⟨22, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20827718738217 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (8924611843 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_23 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20819123145389 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223115697169 / 10000000000000 : ℝ))
      (E := (cell12870 ⟨23, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20819123145389 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223115697169 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_24 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83242134311371 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139447560881 / 6250000000000 : ℝ))
      (E := (cell12870 ⟨24, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83242134311371 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139447560881 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_25 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83207800109909 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231165029379 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨25, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83207800109909 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231165029379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_26 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (10396686243117 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115584511751 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨26, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (10396686243117 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115584511751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_27 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83139203784381 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115586508693 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨27, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83139203784381 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115586508693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_28 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83104941596339 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139448563333 / 6250000000000 : ℝ))
      (E := (cell12870 ⟨28, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83104941596339 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (139448563333 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_29 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (16614140669813 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231181013399 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨29, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (16614140669813 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231181013399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_30 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41518244505489 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231185019439 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨30, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41518244505489 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231185019439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_31 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (83002298550657 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115594516529 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨31, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (83002298550657 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115594516529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_32 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41484065968421 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (55779826391 / 2500000000000 : ℝ))
      (E := (cell12870 ⟨32, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41484065968421 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (55779826391 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_33 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82933989138431 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (111559851487 / 5000000000000 : ℝ))
      (E := (cell12870 ⟨33, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82933989138431 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (111559851487 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_34 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82899870124481 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278900134183 / 12500000000000 : ℝ))
      (E := (cell12870 ⟨34, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82899870124481 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278900134183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_35 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20716443716051 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278900633787 / 12500000000000 : ℝ))
      (E := (cell12870 ⟨35, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20716443716051 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278900633787 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_36 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (8283170332697 / 10000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231209079317 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨36, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (8283170332697 / 10000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231209079317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_37 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (16559531096461 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231213042089 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨37, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (16559531096461 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231213042089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_38 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41381815649943 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231217076013 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨38, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41381815649943 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231217076013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_39 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82729630749547 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231221063491 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨39, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82729630749547 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231221063491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12871_20 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41689851793243 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (139439216011 / 6250000000000 : ℝ))
      (E := (cell12871 ⟨20, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41689851793243 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (139439216011 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_21 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (10418159152489 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (3485986693 / 156250000000 : ℝ))
      (E := (cell12871 ⟨21, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (10418159152489 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (3485986693 / 156250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_22 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16662173403869 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231035496331 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨22, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16662173403869 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231035496331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_23 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83276484952047 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231039498077 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨23, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83276484952047 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231039498077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_24 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83242126985453 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231043491987 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨24, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83242126985453 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231043491987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_25 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (2080194827179 / 2500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231047481061 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨25, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (2080194827179 / 2500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231047481061 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_26 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16634696644987 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231051468059 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨26, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16634696644987 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231051468059 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_27 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83139197366707 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231055513973 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨27, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83139197366707 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231055513973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_28 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (83104935480573 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446211900841 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨28, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (83104935480573 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446211900841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_29 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (20767674383697 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231063499261 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨29, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (20767674383697 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231063499261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_30 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (20759120874443 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115533750489 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨30, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (20759120874443 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115533750489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_31 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41501146669053 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231071510967 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨31, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41501146669053 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231071510967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_32 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82968127024529 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223107553061 / 10000000000000 : ℝ))
      (E := (cell12871 ⟨32, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82968127024529 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (223107553061 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_33 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (4146699226297 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (17430308613 / 781250000000 : ℝ))
      (E := (cell12871 ⟨33, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (4146699226297 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (17430308613 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_34 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41449932905699 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231083544631 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨34, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41449932905699 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231083544631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_35 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16573154170023 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231087540597 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨35, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16573154170023 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231087540597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_36 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41415849805731 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231091549439 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨36, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41415849805731 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231091549439 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_37 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16559530412993 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446219114283 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨37, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16559530412993 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446219114283 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_38 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82763628180303 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557774886961 / 25000000000000 : ℝ))
      (E := (cell12871 ⟨38, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82763628180303 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557774886961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_39 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (8272962792731 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115551768603 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨39, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (8272962792731 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115551768603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12872_20 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (83379695045213 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278863743773 / 12500000000000 : ℝ))
      (E := (cell12872 ⟨20, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (83379695045213 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278863743773 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_21 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41672632491733 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557728491737 / 25000000000000 : ℝ))
      (E := (cell12872 ⟨21, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41672632491733 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557728491737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_22 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (83310859087299 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230917969881 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨22, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (83310859087299 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230917969881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_23 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (83276477323979 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230921962447 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨23, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (83276477323979 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230921962447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_24 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41621059830469 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115463003133 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨24, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41621059830469 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115463003133 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_25 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41603893032889 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230929987579 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨25, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41603893032889 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230929987579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_26 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16634695301253 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230933967513 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨26, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16634695301253 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230933967513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_27 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (83139190950329 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115469003529 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨27, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (83139190950329 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115469003529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_28 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41552464683033 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230941991617 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨28, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41552464683033 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230941991617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_29 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41535345860867 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115472990847 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨29, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41535345860867 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115472990847 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_30 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41518238992877 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115475018827 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨30, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41518238992877 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115475018827 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_31 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41501144063353 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230954044073 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨31, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41501144063353 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230954044073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_32 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82968122113331 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230958002263 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨32, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82968122113331 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230958002263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_33 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82933979914529 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446192406101 / 20000000000000 : ℝ))
      (E := (cell12872 ⟨33, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82933979914529 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446192406101 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_34 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41449930749679 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446193202511 / 20000000000000 : ℝ))
      (E := (cell12872 ⟨34, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41449930749679 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (446193202511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_35 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41432883418517 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (69717814573 / 3125000000000 : ℝ))
      (E := (cell12872 ⟨35, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41432883418517 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (69717814573 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_36 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41415847948463 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (111548703753 / 5000000000000 : ℝ))
      (E := (cell12872 ⟨36, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41415847948463 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (111548703753 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_37 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41398824324281 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230978038913 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨37, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41398824324281 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230978038913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_38 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82763625061621 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557745518823 / 25000000000000 : ℝ))
      (E := (cell12872 ⟨38, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82763625061621 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557745518823 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_39 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41364812552969 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230986066599 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨39, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41364812552969 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230986066599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12873_20 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (8337968650549 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557698124681 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨20, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (8337968650549 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557698124681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_21 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83345256748531 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557699126243 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨21, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83345256748531 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557699126243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_22 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83310851156729 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115400249043 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨22, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83310851156729 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115400249043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_23 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (1665529393947 / 2000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230804539899 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨23, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (1665529393947 / 2000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230804539899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_24 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (20810528084457 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557702129233 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨24, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (20810528084457 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557702129233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_25 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (20801944761441 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230812548933 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨25, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (20801944761441 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230812548933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_26 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41586734894463 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278852065233 / 12500000000000 : ℝ))
      (E := (cell12873 ⟨26, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41586734894463 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278852065233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_27 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (16627836907049 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230820555101 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨27, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (16627836907049 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230820555101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_28 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41552461626409 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230824534047 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨28, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41552461626409 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230824534047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_29 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (83070685909903 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446165703841 / 20000000000000 : ℝ))
      (E := (cell12873 ⟨29, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (83070685909903 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446165703841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_30 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41518236237461 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230832570941 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨30, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41518236237461 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230832570941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_31 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (10375285364557 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230836573827 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨31, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (10375285364557 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230836573827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_32 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82968117203247 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278855073469 / 12500000000000 : ℝ))
      (E := (cell12873 ⟨32, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82968117203247 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278855073469 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_33 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82933975304197 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557711138817 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨33, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82933975304197 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557711138817 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_34 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41449928594181 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (27885607431 / 1250000000000 : ℝ))
      (E := (cell12873 ⟨34, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41449928594181 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (27885607431 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_35 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (64738877207 / 78125000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557713147217 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨35, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (64738877207 / 78125000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557713147217 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_36 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41415846091681 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230856597511 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨36, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41415846091681 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230856597511 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_37 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41398822616547 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557715140493 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨37, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41398822616547 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557715140493 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_38 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (517272637149 / 625000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557716149911 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨38, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (517272637149 / 625000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557716149911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_39 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82729622285431 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557717148233 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨39, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82729622285431 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557717148233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12874_20 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨20, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20844919491829 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (139417190219 / 6250000000000 : ℝ))
      (E := (cell12874 ⟨20, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨20, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20844919491829 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (139417190219 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_21 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨21, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (8334524851511 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230679039271 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨21, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨21, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (8334524851511 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230679039271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_22 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨22, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20827710806909 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230683080947 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨22, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨22, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20827710806909 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230683080947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_23 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨23, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83276462072161 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230687055337 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨23, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨23, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83276462072161 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230687055337 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_24 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨24, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83242105016121 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115345541187 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨24, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨24, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83242105016121 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115345541187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_25 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨25, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83207772027117 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230695106713 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨25, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨25, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83207772027117 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230695106713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_26 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨26, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83173463072917 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230699072679 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨26, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨26, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83173463072917 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230699072679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_27 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨27, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (16627835624291 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446140619929 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨27, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨27, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (16627835624291 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446140619929 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_28 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨28, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20776229285207 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446141414603 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨28, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨28, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20776229285207 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446141414603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_29 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨29, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41535340049647 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230711111797 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨29, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨29, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41535340049647 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230711111797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_30 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨30, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20759116741319 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115357550419 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨30, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨30, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20759116741319 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115357550419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_31 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨31, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (83002277707357 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557679775057 / 25000000000000 : ℝ))
      (E := (cell12874 ⟨31, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨31, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (83002277707357 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557679775057 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_32 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨32, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82968112294279 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557680777837 / 25000000000000 : ℝ))
      (E := (cell12874 ⟨32, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨32, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82968112294279 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557680777837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_33 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨33, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82933970694943 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230727135351 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨33, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨33, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82933970694943 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230727135351 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_34 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨34, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (10362481609801 / 12500000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230731114541 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨34, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨34, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (10362481609801 / 12500000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230731114541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_35 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨35, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82865758813893 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115367583421 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨35, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨35, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82865758813893 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115367583421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_36 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨36, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (5176980529423 / 6250000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115369558397 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨36, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨36, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (5176980529423 / 6250000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115369558397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_37 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨37, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82797641818563 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (223074314059 / 10000000000000 : ℝ))
      (E := (cell12874 ⟨37, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨37, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82797641818563 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (223074314059 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_38 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨38, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41381809413479 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230747179617 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨38, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨38, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41381809413479 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230747179617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_39 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨39, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82729619465789 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446150234989 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨39, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨39, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82729619465789 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446150234989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

end BstLean.Part268
