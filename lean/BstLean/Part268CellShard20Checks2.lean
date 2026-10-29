import BstLean.Part268CellShard20Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12850_40 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41347852240929 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446716249397 / 20000000000000 : ℝ))
      (E := (cell12850 ⟨40, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41347852240929 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446716249397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_41 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82661745167793 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116792630681 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨41, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82661745167793 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116792630681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_42 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82627809404397 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233589272453 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨42, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82627809404397 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233589272453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_43 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82593897162091 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223359327921 / 10000000000000 : ℝ))
      (E := (cell12850 ⟨43, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82593897162091 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223359327921 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_44 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41280004205723 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446719456073 / 20000000000000 : ℝ))
      (E := (cell12850 ⟨44, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41280004205723 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446719456073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_45 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (4126307156159 / 5000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446720254887 / 20000000000000 : ℝ))
      (E := (cell12850 ⟨45, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (4126307156159 / 5000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446720254887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_46 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41246150634079 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233605259723 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨46, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41246150634079 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233605259723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_47 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82458482817393 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233609293239 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨47, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82458482817393 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233609293239 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_48 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (41212343871021 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233613313977 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨48, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (41212343871021 / 50000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233613313977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_49 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82390916013407 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446723463919 / 20000000000000 : ℝ))
      (E := (cell12850 ⟨49, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82390916013407 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (446723463919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_50 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82357167602933 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233621307541 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨50, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82357167602933 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233621307541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_51 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (2572607577569 / 3125000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233625334069 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨51, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (2572607577569 / 3125000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233625334069 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_52 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20572435155741 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233629337229 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨52, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20572435155741 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233629337229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_53 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (5141003874817 / 6250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558408328459 / 25000000000000 : ℝ))
      (E := (cell12850 ⟨53, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (5141003874817 / 6250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558408328459 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_54 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (16444481315309 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233637319583 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨54, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (16444481315309 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233637319583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_55 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (16437754866707 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (279205168867 / 12500000000000 : ℝ))
      (E := (cell12850 ⟨55, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (16437754866707 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (279205168867 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_56 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (20538791310083 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233645345017 / 100000000000000 : ℝ))
      (E := (cell12850 ⟨56, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (20538791310083 / 25000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (2233645345017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_57 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (16424315853873 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116824678483 / 50000000000000 : ℝ))
      (E := (cell12850 ⟨57, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (16424315853873 / 20000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (1116824678483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_58 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (205220040983 / 250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223365338263 / 10000000000000 : ℝ))
      (E := (cell12850 ⟨58, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (205220040983 / 250000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (223365338263 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12850_59 : CellCertificate 12850 (882547001325949 / 10000000000000000 : ℝ) (326915923546393 / 200000000000000000 : ℝ) (66017052037419 / 2000000000000000 : ℝ)
    (cell12850 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · norm_num [cell12850]
  · have h := gap_lower (n := 12850) (a := (82054476584541 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558414339609 / 25000000000000 : ℝ))
      (E := (cell12850 ⟨59, by decide⟩).energy) (xi := (66017052037419 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12850 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12850]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12850])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12850) (a := (82054476584541 / 100000000000000 : ℝ)) (b := (160273419151 / 100000000000000 : ℝ)) (q := (558414339609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12850])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12850]

theorem cert12851_40 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (20673925484979 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446692627511 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨40, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (20673925484979 / 25000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446692627511 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_41 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (5166358932693 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116733577101 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨41, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (5166358932693 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116733577101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_42 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82627807456519 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (8933884673 / 400000000000 : ℝ))
      (E := (cell12851 ⟨42, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82627807456519 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (8933884673 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_43 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (10324236938829 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233475178647 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨43, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (10324236938829 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233475178647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_44 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82560007055997 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233479184127 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨44, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82560007055997 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233479184127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_45 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (16505228412667 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446696636641 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨45, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (16505228412667 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446696636641 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_46 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (8249230050351 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116743616543 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨46, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (8249230050351 / 10000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116743616543 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_47 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (16491696469507 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233491214073 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨47, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (16491696469507 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233491214073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_48 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82424687566569 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446699048373 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨48, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82424687566569 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446699048373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_49 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (16478183226383 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233499255219 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨49, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (16478183226383 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233499255219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_50 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41178584007509 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (111675162579 / 5000000000000 : ℝ))
      (E := (cell12851 ⟨50, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41178584007509 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (111675162579 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_51 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82323443187467 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233507228183 / 100000000000000 : ℝ))
      (E := (cell12851 ⟨51, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82323443187467 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (2233507228183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_52 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (16457948324199 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558377810273 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨52, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (16457948324199 / 20000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558377810273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_53 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82256063287473 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116757643597 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨53, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82256063287473 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116757643597 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_54 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41111204079457 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (111675962249 / 5000000000000 : ℝ))
      (E := (cell12851 ⟨54, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41111204079457 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (111675962249 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_55 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (5136798512967 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558380822029 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨55, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (5136798512967 / 6250000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558380822029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_56 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41077583702719 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446705458931 / 20000000000000 : ℝ))
      (E := (cell12851 ⟨56, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41077583702719 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (446705458931 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_57 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (82121581725241 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116765659869 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨57, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (82121581725241 / 100000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116765659869 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_58 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (10261002392431 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116767650013 / 50000000000000 : ℝ))
      (E := (cell12851 ⟨58, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (10261002392431 / 12500000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (1116767650013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12851_59 : CellCertificate 12851 (11031496114267 / 125000000000000 : ℝ) (163445238166167 / 100000000000000000 : ℝ) (13202358532691 / 400000000000000 : ℝ)
    (cell12851 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · norm_num [cell12851]
  · have h := gap_lower (n := 12851) (a := (41027239810381 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558384822573 / 25000000000000 : ℝ))
      (E := (cell12851 ⟨59, by decide⟩).energy) (xi := (13202358532691 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12851 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12851]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12851])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12851) (a := (41027239810381 / 50000000000000 : ℝ)) (b := (160260799073 / 100000000000000 : ℝ)) (q := (558384822573 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12851])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12851]

theorem cert12852_40 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (10336962424851 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139584071413 / 6250000000000 : ℝ))
      (E := (cell12852 ⟨40, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (10336962424851 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139584071413 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_41 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41330870339591 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233349102823 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨41, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41330870339591 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233349102823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_42 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (16525561101881 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116676559943 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨42, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (16525561101881 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116676559943 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_43 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82593893859901 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233357133983 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨43, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82593893859901 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233357133983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_44 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41280002850621 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233361143847 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨44, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41280002850621 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233361143847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_45 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (41263070502073 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116682573997 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨45, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (41263070502073 / 50000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116682573997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_46 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82492299739483 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116684572361 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨46, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82492299739483 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116684572361 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_47 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (10307310234783 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558343297761 / 25000000000000 : ℝ))
      (E := (cell12852 ⟨47, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (10307310234783 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558343297761 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_48 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (2575771480989 / 3125000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233377167001 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨48, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (2575771480989 / 3125000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233377167001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_49 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82390916250939 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116690594063 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨49, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82390916250939 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116690594063 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_50 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82357168427583 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233385192939 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨50, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82357168427583 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233385192939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_51 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (20580860973293 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139586823667 / 6250000000000 : ℝ))
      (E := (cell12852 ⟨51, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (20580860973293 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (139586823667 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_52 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (20572435654859 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233393201391 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨52, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (20572435654859 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233393201391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_53 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82256064578249 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233397198913 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨53, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82256064578249 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233397198913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_54 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (10277801217703 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233401226931 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨54, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (10277801217703 / 12500000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233401226931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_55 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (20547194520429 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116702611397 / 50000000000000 : ℝ))
      (E := (cell12852 ⟨55, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (20547194520429 / 25000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (1116702611397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_56 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (16431033914163 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558352310457 / 25000000000000 : ℝ))
      (E := (cell12852 ⟨56, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (16431033914163 / 20000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558352310457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_57 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82121584181353 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233413280081 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨57, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82121584181353 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233413280081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_58 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82088021885897 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558354318553 / 25000000000000 : ℝ))
      (E := (cell12852 ⟨58, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82088021885897 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (558354318553 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12852_59 : CellCertificate 12852 (441246190516477 / 5000000000000000 : ℝ) (1634325165398003 / 1000000000000000000 : ℝ) (330032670683247 / 10000000000000000 : ℝ)
    (cell12852 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · norm_num [cell12852]
  · have h := gap_lower (n := 12852) (a := (82054482657151 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233421278997 / 100000000000000 : ℝ))
      (E := (cell12852 ⟨59, by decide⟩).energy) (xi := (330032670683247 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12852 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12852]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12852])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12852) (a := (82054482657151 / 100000000000000 : ℝ)) (b := (80124090497 / 50000000000000 : ℝ)) (q := (2233421278997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12852])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12852]

theorem cert12853_40 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41347848429267 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233227085859 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨40, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41347848429267 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233227085859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_41 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41330869218037 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (89329244289 / 4000000000000 : ℝ))
      (E := (cell12853 ⟨41, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41330869218037 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (89329244289 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_42 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41313901781527 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233235127363 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨42, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41313901781527 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233235127363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_43 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41296946104949 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233239145221 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨43, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41296946104949 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233239145221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_44 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41280002173589 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233243159529 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨44, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41280002173589 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233243159529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_45 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16505227989123 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558311792201 / 25000000000000 : ℝ))
      (E := (cell12853 ⟨45, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16505227989123 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558311792201 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_46 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (82492298976077 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233251171343 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨46, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (82492298976077 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233251171343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_47 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41229240704789 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233255165231 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨47, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41229240704789 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233255165231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_48 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (82424687217277 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116629574169 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨48, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (82424687217277 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116629574169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_49 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41195458185239 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116631588647 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨49, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41195458185239 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116631588647 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_50 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (8235716884063 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233267190617 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨50, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (8235716884063 / 10000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233267190617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_51 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41161722299661 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (111663559277 / 5000000000000 : ℝ))
      (E := (cell12853 ⟨51, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41161722299661 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (111663559277 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_52 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (82289743618287 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (139579701133 / 6250000000000 : ℝ))
      (E := (cell12853 ⟨52, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (82289743618287 / 100000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (139579701133 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_53 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (411280329347 / 500000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558319806549 / 25000000000000 : ℝ))
      (E := (cell12853 ⟨53, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (411280329347 / 500000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (558319806549 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_54 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (3288896452987 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233283206347 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨54, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (3288896452987 / 4000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233283206347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_55 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (16437755991253 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233287214087 / 100000000000000 : ℝ))
      (E := (cell12853 ⟨55, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (16437755991253 / 20000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (2233287214087 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_56 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (5134698233529 / 6250000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116645622837 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨56, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (5134698233529 / 6250000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116645622837 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_57 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41060793318851 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446659047599 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨57, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41060793318851 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446659047599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_58 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (20522006158137 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116649623003 / 50000000000000 : ℝ))
      (E := (cell12853 ⟨58, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (20522006158137 / 25000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (1116649623003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12853_59 : CellCertificate 12853 (882465076999773 / 10000000000000000 : ℝ) (1634197968936341 / 1000000000000000000 : ℝ) (41250797785489 / 1250000000000000 : ℝ)
    (cell12853 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · norm_num [cell12853]
  · have h := gap_lower (n := 12853) (a := (41027242846853 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446660653069 / 20000000000000 : ℝ))
      (E := (cell12853 ⟨59, by decide⟩).energy) (xi := (41250797785489 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12853 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12853]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12853])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12853) (a := (41027242846853 / 50000000000000 : ℝ)) (b := (10014722807 / 6250000000000 : ℝ)) (q := (446660653069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12853])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12853]

theorem cert12854_40 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41347847159547 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (279138642949 / 12500000000000 : ℝ))
      (E := (cell12854 ⟨40, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41347847159547 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (279138642949 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_41 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (16532347238753 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233113108623 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨41, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (16532347238753 / 20000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233113108623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_42 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41313900808733 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (69784910371 / 3125000000000 : ℝ))
      (E := (cell12854 ⟨42, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41313900808733 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (69784910371 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_43 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41296945280311 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116560576763 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨43, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41296945280311 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116560576763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_44 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41280001496903 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558281293079 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨44, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41280001496903 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558281293079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_45 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (4126306944387 / 5000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (17865033023 / 800000000000 : ℝ))
      (E := (cell12854 ⟨45, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (4126306944387 / 5000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (17865033023 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_46 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82492298213293 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558283284059 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨46, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82492298213293 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558283284059 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_47 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41229240470739 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558284298889 / 25000000000000 : ℝ))
      (E := (cell12854 ⟨47, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41229240470739 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (558284298889 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_48 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82424687043457 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139571324117 / 6250000000000 : ℝ))
      (E := (cell12854 ⟨48, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82424687043457 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139571324117 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_49 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41195458245267 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446629032749 / 20000000000000 : ℝ))
      (E := (cell12854 ⟨49, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41195458245267 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446629032749 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_50 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82357169254157 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446629837123 / 20000000000000 : ℝ))
      (E := (cell12854 ⟨50, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82357169254157 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446629837123 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_51 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41161722652959 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233153189763 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨51, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41161722652959 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233153189763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_52 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82289744617549 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233157232257 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨52, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82289744617549 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233157232257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_53 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82256067160927 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (13957257449 / 625000000000 : ℝ))
      (E := (cell12854 ⟨53, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82256067160927 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (13957257449 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_54 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (41111206454033 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233165242317 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨54, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (41111206454033 / 50000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233165242317 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_55 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (1027359772889 / 1250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116584630997 / 50000000000000 : ℝ))
      (E := (cell12854 ⟨55, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (1027359772889 / 1250000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (1116584630997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_56 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82155173902383 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139573327941 / 6250000000000 : ℝ))
      (E := (cell12854 ⟨56, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82155173902383 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (139573327941 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_57 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (82121589094287 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233177252641 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨57, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (82121589094287 / 100000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233177252641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_58 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (410440136897 / 500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233181274591 / 100000000000000 : ℝ))
      (E := (cell12854 ⟨58, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (410440136897 / 500000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (2233181274591 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12854_59 : CellCertificate 12854 (441218888520431 / 5000000000000000 : ℝ) (81703539613603 / 50000000000000000 : ℝ) (82495024529543 / 2500000000000000 : ℝ)
    (cell12854 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · norm_num [cell12854]
  · have h := gap_lower (n := 12854) (a := (20513622182607 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446637049867 / 20000000000000 : ℝ))
      (E := (cell12854 ⟨59, by decide⟩).energy) (xi := (82495024529543 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12854 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12854]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12854])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12854) (a := (20513622182607 / 25000000000000 : ℝ)) (b := (160222950829 / 100000000000000 : ℝ)) (q := (446637049867 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12854])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12854]

theorem cert12855_40 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (10336961472561 / 12500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116495569763 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨40, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (10336961472561 / 12500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116495569763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_41 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82661733952253 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446599033161 / 20000000000000 : ℝ))
      (E := (cell12855 ⟨41, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82661733952253 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446599033161 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_42 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (258211873977 / 312500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116499596113 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨42, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (258211873977 / 312500000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116499596113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_43 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82593888912073 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233003158903 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨43, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82593888912073 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233003158903 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_44 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41280000820563 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233007182209 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨44, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41280000820563 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233007182209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_45 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41263068915261 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233011201847 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨45, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41263068915261 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233011201847 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_46 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82492297451129 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558253804029 / 25000000000000 : ℝ))
      (E := (cell12855 ⟨46, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82492297451129 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (558253804029 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_47 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (16491696094793 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (279127402887 / 12500000000000 : ℝ))
      (E := (cell12855 ⟨47, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (16491696094793 / 20000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (279127402887 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_48 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (20606171717547 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116511610329 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨48, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (20606171717547 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116511610329 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_49 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (2574716144097 / 3125000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116513603229 / 50000000000000 : ℝ))
      (E := (cell12855 ⟨49, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (2574716144097 / 3125000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (1116513603229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_50 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (20589292417041 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233031236933 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨50, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (20589292417041 / 25000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233031236933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_51 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41161723006479 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (34891175787 / 1562500000000 : ℝ))
      (E := (cell12855 ⟨51, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41161723006479 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (34891175787 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_52 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41144872808611 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (111651962189 / 5000000000000 : ℝ))
      (E := (cell12855 ⟨52, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41144872808611 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (111651962189 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_53 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82256068452829 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (44660865461 / 2000000000000 : ℝ))
      (E := (cell12855 ⟨53, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82256068452829 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (44660865461 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_54 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82222414491797 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446609455151 / 20000000000000 : ℝ))
      (E := (cell12855 ⟨54, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82222414491797 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446609455151 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_55 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (2054719592657 / 2500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (223305124829 / 10000000000000 : ℝ))
      (E := (cell12855 ⟨55, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (2054719592657 / 2500000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (223305124829 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_56 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82155176068573 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233055305113 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨56, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82155176068573 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233055305113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_57 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82121591551107 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233059264861 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨57, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82121591551107 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233059264861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_58 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (41044015063227 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446612660157 / 20000000000000 : ℝ))
      (E := (cell12855 ⟨58, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (41044015063227 / 50000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (446612660157 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12855_59 : CellCertificate 12855 (176482096231053 / 2000000000000000 : ℝ) (1633943635400539 / 1000000000000000000 : ℝ) (329953818184927 / 10000000000000000 : ℝ)
    (cell12855 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · norm_num [cell12855]
  · have h := gap_lower (n := 12855) (a := (82054491767317 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233067290177 / 100000000000000 : ℝ))
      (E := (cell12855 ⟨59, by decide⟩).energy) (xi := (329953818184927 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12855 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12855]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12855])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12855) (a := (82054491767317 / 100000000000000 : ℝ)) (b := (80105169371 / 50000000000000 : ℝ)) (q := (2233067290177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12855])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12855]

theorem cert12856_40 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20673922310679 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232873249943 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨40, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20673922310679 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232873249943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_41 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (4133086585577 / 5000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232877219983 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨41, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (4133086585577 / 5000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232877219983 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_42 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (1291059339509 / 1562500000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558220312403 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨42, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (1291059339509 / 1562500000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558220312403 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_43 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (330375549057 / 400000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446577055803 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨43, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (330375549057 / 400000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446577055803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_44 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82560000289137 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446577849613 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨44, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82560000289137 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446577849613 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_45 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82526136773959 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232893272963 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨45, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82526136773959 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232893272963 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_46 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82492296689587 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558224323293 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨46, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82492296689587 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558224323293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_47 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20614620001759 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232901306777 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨47, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20614620001759 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232901306777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_48 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82424686697469 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558226327911 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨48, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82424686697469 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558226327911 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_49 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (8239091673219 / 10000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223290930543 / 10000000000000 : ℝ))
      (E := (cell12856 ⟨49, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (8239091673219 / 10000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223290930543 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_50 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82357170082651 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116456642787 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨50, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82357170082651 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116456642787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_51 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20580861680111 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223291730833 / 10000000000000 : ℝ))
      (E := (cell12856 ⟨51, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20580861680111 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (223291730833 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_52 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (10286218327163 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116460655871 / 50000000000000 : ℝ))
      (E := (cell12856 ⟨52, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (10286218327163 / 12500000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (1116460655871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_53 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82256069745107 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (279115668961 / 12500000000000 : ℝ))
      (E := (cell12856 ⟨53, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82256069745107 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (279115668961 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_54 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82222416075869 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232929365749 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨54, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82222416075869 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232929365749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_55 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (41094392790873 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446586670063 / 20000000000000 : ℝ))
      (E := (cell12856 ⟨55, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (41094392790873 / 50000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (446586670063 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_56 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (82155178235033 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558234340177 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨56, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (82155178235033 / 100000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558234340177 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_57 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20530398502041 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (89317655719 / 4000000000000 : ℝ))
      (E := (cell12856 ⟨57, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20530398502041 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (89317655719 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_58 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20522008218427 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558236345943 / 25000000000000 : ℝ))
      (E := (cell12856 ⟨58, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20522008218427 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (558236345943 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12856_59 : CellCertificate 12856 (35295327573681 / 400000000000000 : ℝ) (1633816498317157 / 1000000000000000000 : ℝ) (8248188562077 / 250000000000000 : ℝ)
    (cell12856 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · norm_num [cell12856]
  · have h := gap_lower (n := 12856) (a := (20513623701093 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232949387871 / 100000000000000 : ℝ))
      (E := (cell12856 ⟨59, by decide⟩).energy) (xi := (8248188562077 / 250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12856 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12856]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12856])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12856) (a := (20513623701093 / 25000000000000 : ℝ)) (b := (160197728653 / 100000000000000 : ℝ)) (q := (2232949387871 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12856])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12856]

theorem cert12857_40 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (5168480419111 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89310214293 / 4000000000000 : ℝ))
      (E := (cell12857 ⟨40, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (5168480419111 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (89310214293 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_41 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (10332716183953 / 12500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232759329947 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨41, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (10332716183953 / 12500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232759329947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_42 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (3305111831411 / 4000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558190840711 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨42, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (3305111831411 / 4000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558190840711 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_43 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (16518777123431 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116383668683 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨43, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (16518777123431 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116383668683 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_44 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (1031999986723 / 1250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558192842471 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨44, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (1031999986723 / 1250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558192842471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_45 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82526135718053 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116387670611 / 50000000000000 : ℝ))
      (E := (cell12857 ⟨45, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82526135718053 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (1116387670611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_46 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (16498459185733 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232779367411 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨46, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (16498459185733 / 20000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232779367411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_47 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82458479540693 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558195846919 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨47, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82458479540693 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558195846919 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_48 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (824246865253 / 1000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558196849971 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨48, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (824246865253 / 1000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558196849971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_49 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82390916853791 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232791401691 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨49, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82390916853791 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232791401691 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_50 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82357170497619 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232795390537 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨50, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82357170497619 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232795390537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_51 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (658587579427 / 800000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232799422673 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨51, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (658587579427 / 800000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232799422673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_52 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20572436904449 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446560687229 / 20000000000000 : ℝ))
      (E := (cell12857 ⟨52, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20572436904449 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (446560687229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_53 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82256071037759 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (27910092847 / 1250000000000 : ℝ))
      (E := (cell12857 ⟨53, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82256071037759 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (27910092847 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_54 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (2055560441507 / 2500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232811453211 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨54, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (2055560441507 / 2500000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232811453211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_55 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (82188787457517 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558203862461 / 25000000000000 : ℝ))
      (E := (cell12857 ⟨55, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (82188787457517 / 100000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (558203862461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_56 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20538795100441 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (111640973649 / 5000000000000 : ℝ))
      (E := (cell12857 ⟨56, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20538795100441 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (111640973649 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_57 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (5132599779091 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232823459503 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨57, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (5132599779091 / 6250000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232823459503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_58 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (20522008905291 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (139551716523 / 6250000000000 : ℝ))
      (E := (cell12857 ⟨58, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (20522008905291 / 25000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (139551716523 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12857_59 : CellCertificate 12857 (220588975400047 / 2500000000000000 : ℝ) (102105586313581 / 62500000000000000 : ℝ) (164950635505767 / 5000000000000000 : ℝ)
    (cell12857 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · norm_num [cell12857]
  · have h := gap_lower (n := 12857) (a := (41027248920797 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232831483211 / 100000000000000 : ℝ))
      (E := (cell12857 ⟨59, by decide⟩).energy) (xi := (164950635505767 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12857 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12857]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12857])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12857) (a := (41027248920797 / 50000000000000 : ℝ)) (b := (160185120559 / 100000000000000 : ℝ)) (q := (2232831483211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12857])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12857]

theorem cert12858_40 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (8269568416967 / 10000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232637461669 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨40, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (8269568416967 / 10000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232637461669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_41 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41330863616253 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232641436911 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨41, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41330863616253 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232641436911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_42 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (5164237115171 / 6250000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232645473111 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨42, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (5164237115171 / 6250000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232645473111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_43 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41296941985393 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116324725811 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨43, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41296941985393 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116324725811 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_44 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82559997587233 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116326744407 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨44, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82559997587233 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116326744407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_45 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41263067331401 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116328732753 / 50000000000000 : ℝ))
      (E := (cell12858 ⟨45, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41263067331401 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (1116328732753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_46 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (20623073792091 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558165374433 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨46, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (20623073792091 / 25000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558165374433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_47 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (10307309884367 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232665524717 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨47, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (10307309884367 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232665524717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_48 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82424686353681 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232669485377 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨48, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82424686353681 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232669485377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_49 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82390916975907 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232673495241 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨49, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82390916975907 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232673495241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_50 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41178585456533 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232677551821 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨50, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41178585456533 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232677551821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_51 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82323448136751 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279085191797 / 12500000000000 : ℝ))
      (E := (cell12858 ⟨51, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82323448136751 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (279085191797 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_52 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41144874309349 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232685557943 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨52, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41144874309349 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232685557943 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_53 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41128036165393 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232689560331 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨53, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41128036165393 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232689560331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_54 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (10277802405629 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232693538141 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨54, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (10277802405629 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232693538141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_55 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82188789333593 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558174386719 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨55, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82188789333593 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558174386719 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_56 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41077591284383 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232701582789 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨56, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41077591284383 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232701582789 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_57 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (10265199865373 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232705582767 / 100000000000000 : ℝ))
      (E := (cell12858 ⟨57, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (10265199865373 / 12500000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (2232705582767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_58 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (82088038368821 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (13954435011 / 625000000000 : ℝ))
      (E := (cell12858 ⟨58, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (82088038368821 / 100000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (13954435011 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12858_59 : CellCertificate 12858 (441164308964399 / 5000000000000000 : ℝ) (1633562283496339 / 1000000000000000000 : ℝ) (41234375471149 / 1250000000000000 : ℝ)
    (cell12858 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · norm_num [cell12858]
  · have h := gap_lower (n := 12858) (a := (41027250439491 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558178394049 / 25000000000000 : ℝ))
      (E := (cell12858 ⟨59, by decide⟩).energy) (xi := (41234375471149 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12858 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12858]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12858])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12858) (a := (41027250439491 / 50000000000000 : ℝ)) (b := (160172514461 / 100000000000000 : ℝ)) (q := (558178394049 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12858])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12858]

theorem cert12859_40 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20673920408599 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232519621741 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨40, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20673920408599 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232519621741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_41 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (16532344998837 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (111626179983 / 5000000000000 : ℝ))
      (E := (cell12859 ⟨41, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (16532344998837 / 20000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (111626179983 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_42 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41313895950479 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (89301105569 / 4000000000000 : ℝ))
      (E := (cell12859 ⟨42, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41313895950479 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (89301105569 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_43 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82593882325143 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446506324357 / 20000000000000 : ℝ))
      (E := (cell12859 ⟨43, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82593882325143 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446506324357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_44 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41279998118659 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232535604851 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨44, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41279998118659 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232535604851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_45 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82526133608207 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (279067455727 / 12500000000000 : ℝ))
      (E := (cell12859 ⟨45, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82526133608207 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (279067455727 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_46 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41246147204341 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232543625237 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨46, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41246147204341 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232543625237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_47 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82458478609763 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232547658977 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨47, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82458478609763 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232547658977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_48 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20606171545653 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232551686023 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨48, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20606171545653 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232551686023 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_49 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41195458549269 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116277822527 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨49, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41195458549269 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116277822527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_50 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (2573661604031 / 3125000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446511930287 / 20000000000000 : ℝ))
      (E := (cell12859 ⟨50, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (2573661604031 / 3125000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446511930287 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_51 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82323448845571 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116281851231 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨51, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82323448845571 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116281851231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_52 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (8228974962001 / 10000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232567677139 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨52, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (8228974962001 / 10000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232567677139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_53 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20564018406047 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446514338067 / 20000000000000 : ℝ))
      (E := (cell12859 ⟨53, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20564018406047 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (446514338067 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_54 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82222420830123 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232575738721 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨54, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82222420830123 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232575738721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_55 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41094395604987 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232579700527 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨55, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41094395604987 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232579700527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_56 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (82155184736037 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116291874639 / 50000000000000 : ℝ))
      (E := (cell12859 ⟨56, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (82155184736037 / 100000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (1116291874639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_57 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (20530400345187 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232587762767 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨57, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (20530400345187 / 25000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232587762767 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_58 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (41044020558339 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232591736763 / 100000000000000 : ℝ))
      (E := (cell12859 ⟨58, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (41044020558339 / 50000000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (2232591736763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12859_59 : CellCertificate 12859 (8823013383269 / 100000000000000 : ℝ) (1633435205749669 / 1000000000000000000 : ℝ) (164924370377479 / 5000000000000000 : ℝ)
    (cell12859 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · norm_num [cell12859]
  · have h := gap_lower (n := 12859) (a := (10256812989567 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558148946311 / 25000000000000 : ℝ))
      (E := (cell12859 ⟨59, by decide⟩).energy) (xi := (164924370377479 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12859 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12859]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12859])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12859) (a := (10256812989567 / 12500000000000 : ℝ)) (b := (80079955179 / 50000000000000 : ℝ)) (q := (558148946311 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12859])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12859]

theorem cert12860_40 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41347839549977 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116200889389 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨40, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41347839549977 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116200889389 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_41 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (4133086137833 / 5000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116202909099 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨41, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (4133086137833 / 5000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116202909099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_42 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82627789959941 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232409802377 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨42, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82627789959941 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232409802377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_43 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41296940340113 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232413789021 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨43, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41296940340113 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232413789021 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_44 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82559994888093 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34881528683 / 1562500000000 : ℝ))
      (E := (cell12860 ⟨44, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82559994888093 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (34881528683 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_45 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82526132554267 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232421823271 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨45, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82526132554267 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232421823271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_46 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82492293649621 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116212904413 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨46, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82492293649621 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116212904413 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_47 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (3298339125807 / 4000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232429849381 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨47, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (3298339125807 / 4000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232429849381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_48 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20606171503023 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116216912487 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨48, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20606171503023 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116216912487 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_49 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41195458610841 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558109462783 / 25000000000000 : ℝ))
      (E := (cell12860 ⟨49, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41195458610841 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (558109462783 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_50 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41178585872699 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (17440952081 / 781250000000 : ℝ))
      (E := (cell12860 ⟨50, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41178585872699 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (17440952081 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_51 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (16464689910967 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232445867911 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨51, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (16464689910967 / 20000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232445867911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_52 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82289750621731 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232449852777 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨52, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82289750621731 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232449852777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_53 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (20564018729491 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232453876841 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨53, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (20564018729491 / 25000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232453876841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_54 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (41111211207777 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (27905723471 / 1250000000000 : ℝ))
      (E := (cell12860 ⟨54, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (41111211207777 / 50000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (27905723471 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_55 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (4109439654333 / 5000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232461910797 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨55, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (4109439654333 / 5000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232461910797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_56 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82155186903579 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232465913307 / 100000000000000 : ℝ))
      (E := (cell12860 ⟨56, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82155186903579 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (2232465913307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_57 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82121603838747 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (279058742543 / 12500000000000 : ℝ))
      (E := (cell12860 ⟨57, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82121603838747 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (279058742543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_58 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (2565251370773 / 3125000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116236964281 / 50000000000000 : ℝ))
      (E := (cell12860 ⟨58, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (2565251370773 / 3125000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (1116236964281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12860_59 : CellCertificate 12860 (44113703139677 / 500000000000000 : ℝ) (6380109952237 / 3906250000000000 : ℝ) (329822481967737 / 10000000000000000 : ℝ)
    (cell12860 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · norm_num [cell12860]
  · have h := gap_lower (n := 12860) (a := (82054506954257 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223247793273 / 10000000000000 : ℝ))
      (E := (cell12860 ⟨59, by decide⟩).energy) (xi := (329822481967737 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12860 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12860]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12860])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12860) (a := (82054506954257 / 100000000000000 : ℝ)) (b := (640589233 / 400000000000 : ℝ)) (q := (223247793273 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12860])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12860]

theorem cert12861_40 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16539135313269 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232283991543 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨40, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16539135313269 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232283991543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_41 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82661720519933 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232287974951 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨41, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82661720519933 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232287974951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_42 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41313894009843 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232292021377 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨42, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41313894009843 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232292021377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_43 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16518775807207 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446459202433 / 20000000000000 : ℝ))
      (E := (cell12861 ⟨43, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16518775807207 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (446459202433 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_44 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41279996769779 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558075001207 / 25000000000000 : ℝ))
      (E := (cell12861 ⟨44, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41279996769779 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558075001207 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_45 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41263065750491 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (17858431983 / 800000000000 : ℝ))
      (E := (cell12861 ⟨45, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41263065750491 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (17858431983 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_46 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (4124614644559 / 5000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116154024251 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨46, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (4124614644559 / 5000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116154024251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_47 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82458477681171 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116156018503 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨47, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82458477681171 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116156018503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_48 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41212342921061 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232316079081 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨48, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41212342921061 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232316079081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_49 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (41195458672671 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (4464640109 / 200000000000 : ℝ))
      (E := (cell12861 ⟨49, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (41195458672671 / 50000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (4464640109 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_50 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (20589293040571 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558081019657 / 25000000000000 : ℝ))
      (E := (cell12861 ⟨50, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (20589293040571 / 25000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (558081019657 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_51 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (2572607820767 / 3125000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116164044871 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨51, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (2572607820767 / 3125000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116164044871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_52 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82289751623861 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116166042429 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨52, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82289751623861 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116166042429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_53 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16451215242423 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232336060781 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨53, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16451215242423 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232336060781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_54 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (3288896960053 / 4000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (5580850183 / 250000000000 : ℝ))
      (E := (cell12861 ⟨54, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (3288896960053 / 4000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (5580850183 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_55 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82188794963651 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232344118573 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨55, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82188794963651 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232344118573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_56 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (8215518907139 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (17440219797 / 781250000000 : ℝ))
      (E := (cell12861 ⟨56, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (8215518907139 / 10000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (17440219797 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_57 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82121606296981 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116176057749 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨57, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82121606296981 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116176057749 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_58 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (16417609322599 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232356117973 / 100000000000000 : ℝ))
      (E := (cell12861 ⟨58, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (16417609322599 / 20000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (2232356117973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12861_59 : CellCertificate 12861 (220561697831941 / 2500000000000000 : ℝ) (326636221912147 / 200000000000000000 : ℝ) (329796227406431 / 10000000000000000 : ℝ)
    (cell12861 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · norm_num [cell12861]
  · have h := gap_lower (n := 12861) (a := (82054509992143 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116180068537 / 50000000000000 : ℝ))
      (E := (cell12861 ⟨59, by decide⟩).energy) (xi := (329796227406431 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12861 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12861]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12861])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12861) (a := (82054509992143 / 100000000000000 : ℝ)) (b := (20016838517 / 12500000000000 : ℝ)) (q := (1116180068537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12861])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12861]

theorem cert12862_40 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (2584239813549 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116083100637 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨40, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (2584239813549 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116083100637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_41 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82661718284001 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232170246281 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨41, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82661718284001 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232170246281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_42 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (1291059157503 / 1562500000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279021779677 / 12500000000000 : ℝ))
      (E := (cell12862 ⟨42, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (1291059157503 / 1562500000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (279021779677 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_43 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (8259387739257 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (34877784881 / 1562500000000 : ℝ))
      (E := (cell12862 ⟨43, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (8259387739257 / 10000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (34877784881 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_44 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41279996095857 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232182229911 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨44, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41279996095857 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232182229911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_45 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (2578941576511 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446437257477 / 20000000000000 : ℝ))
      (E := (cell12862 ⟨45, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (2578941576511 / 3125000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446437257477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_46 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41246146066679 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116095142681 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨46, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41246146066679 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116095142681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_47 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (10307309652219 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232194280777 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨47, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (10307309652219 / 12500000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232194280777 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_48 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82424685672701 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232198271493 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨48, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82424685672701 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232198271493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_49 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (16478183493903 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446440462827 / 20000000000000 : ℝ))
      (E := (cell12862 ⟨49, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (16478183493903 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446440462827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_50 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (1286830821557 / 1562500000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232206288217 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨50, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (1286830821557 / 1562500000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232206288217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_51 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82323450974697 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116105154469 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨51, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82323450974697 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116105154469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_52 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (82289752626401 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116107157169 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨52, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (82289752626401 / 100000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116107157169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_53 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (1028200968833 / 1250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232218301223 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨53, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (1028200968833 / 1250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232218301223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_54 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (16444485117487 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116111162641 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨54, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (16444485117487 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116111162641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_55 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41094398420473 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (139514145241 / 6250000000000 : ℝ))
      (E := (cell12862 ⟨55, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41094398420473 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (139514145241 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_56 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (5134699452467 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446446070453 / 20000000000000 : ℝ))
      (E := (cell12862 ⟨56, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (5134699452467 / 6250000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (446446070453 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_57 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (1642432175109 / 2000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (223223434739 / 10000000000000 : ℝ))
      (E := (cell12862 ⟨57, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (1642432175109 / 2000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (223223434739 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_58 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (41044024680727 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232238364183 / 100000000000000 : ℝ))
      (E := (cell12862 ⟨58, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (41044024680727 / 50000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (2232238364183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12862_59 : CellCertificate 12862 (882219523928617 / 10000000000000000 : ℝ) (816527045554623 / 500000000000000000 : ℝ) (82442494267487 / 2500000000000000 : ℝ)
    (cell12862 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · norm_num [cell12862]
  · have h := gap_lower (n := 12862) (a := (16410902606039 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116121199137 / 50000000000000 : ℝ))
      (E := (cell12862 ⟨59, by decide⟩).energy) (xi := (82442494267487 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12862 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12862]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12862])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12862) (a := (16410902606039 / 20000000000000 : ℝ)) (b := (2501907969 / 1562500000000 : ℝ)) (q := (1116121199137 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12862])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12862]

theorem cert12863_40 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41347835750811 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139503029171 / 6250000000000 : ℝ))
      (E := (cell12863 ⟨40, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41347835750811 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139503029171 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_41 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41330858024433 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116026257307 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨41, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41330858024433 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116026257307 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_42 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41313892070729 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446411301861 / 20000000000000 : ℝ))
      (E := (cell12863 ⟨42, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41313892070729 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446411301861 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_43 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82593875749829 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116030254257 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨43, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82593875749829 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116030254257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_44 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82559990844559 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446412902193 / 20000000000000 : ℝ))
      (E := (cell12863 ⟨44, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82559990844559 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446412902193 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_45 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (10315766174547 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446413703033 / 20000000000000 : ℝ))
      (E := (cell12863 ⟨45, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (10315766174547 / 12500000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446413703033 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_46 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16498458275231 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139504532463 / 6250000000000 : ℝ))
      (E := (cell12863 ⟨46, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16498458275231 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (139504532463 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_47 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82458476754917 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232076521769 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨47, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82458476754917 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232076521769 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_48 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82424685503829 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232080520113 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨48, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82424685503829 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232080520113 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_49 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41195458797101 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232084571063 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨49, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41195458797101 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232084571063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_50 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82357172997491 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (558022138533 / 25000000000000 : ℝ))
      (E := (cell12863 ⟨50, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82357172997491 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (558022138533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_51 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82323451685293 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232092584519 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨51, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82323451685293 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232092584519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_52 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82289753629349 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232096600263 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨52, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82289753629349 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232096600263 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_53 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82256078801539 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (223210059817 / 10000000000000 : ℝ))
      (E := (cell12863 ⟨53, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82256078801539 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (223210059817 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_54 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (20555606793471 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446420914967 / 20000000000000 : ℝ))
      (E := (cell12863 ⟨54, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (20555606793471 / 25000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (446420914967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_55 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (16437759743709 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116054292881 / 50000000000000 : ℝ))
      (E := (cell12863 ⟨55, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (16437759743709 / 20000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (1116054292881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_56 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82155193407823 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232112627197 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨56, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82155193407823 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232112627197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_57 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (41060805607077 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (279014579503 / 12500000000000 : ℝ))
      (E := (cell12863 ⟨57, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (41060805607077 / 50000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (279014579503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_58 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82088052110113 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232120608007 / 100000000000000 : ℝ))
      (E := (cell12863 ⟨58, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82088052110113 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (2232120608007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12863_59 : CellCertificate 12863 (441096130297573 / 5000000000000000 : ℝ) (408231773103399 / 250000000000000000 : ℝ) (41217966369649 / 1250000000000000 : ℝ)
    (cell12863 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · norm_num [cell12863]
  · have h := gap_lower (n := 12863) (a := (82054516068413 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (558031164281 / 25000000000000 : ℝ))
      (E := (cell12863 ⟨59, by decide⟩).energy) (xi := (41217966369649 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12863 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12863]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12863])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12863) (a := (82054516068413 / 100000000000000 : ℝ)) (b := (160109513889 / 100000000000000 : ℝ)) (q := (558031164281 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12863])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12863]

theorem cert12864_40 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20673917242627 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278991348491 / 12500000000000 : ℝ))
      (E := (cell12864 ⟨40, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20673917242627 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278991348491 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_41 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82661713814527 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231934779951 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨41, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82661713814527 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231934779951 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_42 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16525556440697 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446387755647 / 20000000000000 : ℝ))
      (E := (cell12864 ⟨42, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16525556440697 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (446387755647 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_43 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41296937053907 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (55798569543 / 2500000000000 : ℝ))
      (E := (cell12864 ⟨43, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41296937053907 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (55798569543 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_44 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16511997899619 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223194678913 / 10000000000000 : ℝ))
      (E := (cell12864 ⟨44, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16511997899619 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223194678913 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_45 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (16505225669011 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (89278031959 / 4000000000000 : ℝ))
      (E := (cell12864 ⟨45, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (16505225669011 / 20000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (89278031959 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_46 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20623072654893 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115977404771 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨46, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20623072654893 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115977404771 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_47 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41229238146333 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223195881891 / 10000000000000 : ℝ))
      (E := (cell12864 ⟨47, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41229238146333 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223195881891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_48 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41212342667753 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231962824941 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨48, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41212342667753 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231962824941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_49 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82390917719403 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557991706321 / 25000000000000 : ℝ))
      (E := (cell12864 ⟨49, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82390917719403 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557991706321 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_50 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82357173415813 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115985438187 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨50, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82357173415813 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115985438187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_51 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41161726198167 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278996857183 / 12500000000000 : ℝ))
      (E := (cell12864 ⟨51, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41161726198167 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278996857183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_52 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (41144877316353 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231978883589 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨52, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (41144877316353 / 50000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231978883589 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_53 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82256080096811 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115991446277 / 50000000000000 : ℝ))
      (E := (cell12864 ⟨53, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82256080096811 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (1115991446277 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_54 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (2569450898771 / 3125000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231986880953 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨54, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (2569450898771 / 3125000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231986880953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_55 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82188800596449 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231990904289 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨55, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82188800596449 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2231990904289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_56 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82155195576443 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278999362459 / 12500000000000 : ℝ))
      (E := (cell12864 ⟨56, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82155195576443 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (278999362459 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_57 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82121613673093 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557999730559 / 25000000000000 : ℝ))
      (E := (cell12864 ⟨57, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82121613673093 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (557999730559 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_58 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (82088054858973 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223200290863 / 10000000000000 : ℝ))
      (E := (cell12864 ⟨58, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (82088054858973 / 100000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (223200290863 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12864_59 : CellCertificate 12864 (441082500663199 / 5000000000000000 : ℝ) (65312004538767 / 40000000000000000 : ℝ) (329717489067069 / 10000000000000000 : ℝ)
    (cell12864 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · norm_num [cell12864]
  · have h := gap_lower (n := 12864) (a := (20513629776699 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2232006913623 / 100000000000000 : ℝ))
      (E := (cell12864 ⟨59, by decide⟩).energy) (xi := (329717489067069 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12864 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12864]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12864])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12864) (a := (20513629776699 / 25000000000000 : ℝ)) (b := (32019383951 / 20000000000000 : ℝ)) (q := (2232006913623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12864])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12864]

theorem cert12865_40 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (3307826657609 / 4000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231813106091 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨40, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (3307826657609 / 4000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231813106091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_41 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (10332713947623 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (55795427527 / 2500000000000 : ℝ))
      (E := (cell12865 ⟨41, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (10332713947623 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (55795427527 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_42 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82627780266273 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446364220603 / 20000000000000 : ℝ))
      (E := (cell12865 ⟨42, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82627780266273 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446364220603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_43 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20648468116631 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115912555419 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨43, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20648468116631 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115912555419 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_44 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82559988152319 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231829123269 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨44, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82559988152319 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231829123269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_45 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20631531823597 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446366627763 / 20000000000000 : ℝ))
      (E := (cell12865 ⟨45, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20631531823597 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (446366627763 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_46 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (10311536232951 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115918577883 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨46, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (10311536232951 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115918577883 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_47 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82458475830999 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (11159205861 / 500000000000 : ℝ))
      (E := (cell12865 ⟨47, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82458475830999 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (11159205861 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_48 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (20606171291933 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231845127027 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨48, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (20606171291933 / 25000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231845127027 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_49 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41195458922559 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231849135773 / 100000000000000 : ℝ))
      (E := (cell12865 ⟨49, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41195458922559 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (2231849135773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_50 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82357173834613 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115926597973 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨50, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82357173834613 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115926597973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_51 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41161726553909 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115928593399 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨51, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41161726553909 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115928593399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_52 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (10286219454559 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557965291079 / 25000000000000 : ℝ))
      (E := (cell12865 ⟨52, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (10286219454559 / 12500000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557965291079 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_53 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41128040696229 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115932592187 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨53, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41128040696229 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115932592187 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_54 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82222430347799 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (69745912017 / 3125000000000 : ℝ))
      (E := (cell12865 ⟨54, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82222430347799 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (69745912017 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_55 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82188802474657 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115936610163 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨55, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82188802474657 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115936610163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_56 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82155197745333 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223187722883 / 10000000000000 : ℝ))
      (E := (cell12865 ⟨56, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82155197745333 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (223187722883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_57 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (41060808066133 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557970301507 / 25000000000000 : ℝ))
      (E := (cell12865 ⟨57, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (41060808066133 / 50000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (557970301507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_58 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (82088057608033 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115942633027 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨58, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (82088057608033 / 100000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115942633027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12865_59 : CellCertificate 12865 (882137746121419 / 10000000000000000 : ℝ) (102042072141961 / 62500000000000000 : ℝ) (329691251398487 / 10000000000000000 : ℝ)
    (cell12865 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · norm_num [cell12865]
  · have h := gap_lower (n := 12865) (a := (16410904429069 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115944613491 / 50000000000000 : ℝ))
      (E := (cell12865 ⟨59, by decide⟩).energy) (xi := (329691251398487 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12865 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12865]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12865])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12865) (a := (16410904429069 / 20000000000000 : ℝ)) (b := (160084327613 / 100000000000000 : ℝ)) (q := (1115944613491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12865])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12865]

theorem cert12866_40 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41347831955387 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231695421223 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨40, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41347831955387 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231695421223 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_41 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20665427337059 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231699419217 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨41, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20665427337059 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231699419217 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_42 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (4131388916491 / 5000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231703424841 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨42, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (4131388916491 / 5000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231703424841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_43 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41296935412979 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446341487407 / 20000000000000 : ℝ))
      (E := (cell12866 ⟨43, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41296935412979 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (446341487407 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_44 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41279993403617 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231711454521 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨44, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41279993403617 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231711454521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_45 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (10315765780547 / 12500000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115857737903 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨45, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (10315765780547 / 12500000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115857737903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_46 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41246144554131 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231719499179 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨46, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41246144554131 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231719499179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_47 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20614618842479 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231723463787 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨47, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20614618842479 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231723463787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_48 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41212342500253 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557931871331 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨48, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41212342500253 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557931871331 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_49 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41195458985673 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231731502533 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨49, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41195458985673 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231731502533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_50 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20589293563473 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (44634710257 / 2000000000000 : ℝ))
      (E := (cell12866 ⟨50, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20589293563473 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (44634710257 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_51 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (16464690763949 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231739513499 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨51, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (16464690763949 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231739513499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_52 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41144878320323 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557935875373 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨52, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41144878320323 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557935875373 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_53 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (41128041344239 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115873766351 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨53, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (41128041344239 / 50000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115873766351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_54 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (16444486387053 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (22317515447 / 1000000000000 : ℝ))
      (E := (cell12866 ⟨54, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (16444486387053 / 20000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (22317515447 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_55 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (82188804353169 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (139484720867 / 6250000000000 : ℝ))
      (E := (cell12866 ⟨55, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (82188804353169 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (139484720867 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_56 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (20538799978623 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115879777767 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨56, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (20538799978623 / 25000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115879777767 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_57 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (3284864743667 / 4000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115881773281 / 50000000000000 : ℝ))
      (E := (cell12866 ⟨57, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (3284864743667 / 4000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (1115881773281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_58 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (82088060357293 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557941890477 / 25000000000000 : ℝ))
      (E := (cell12866 ⟨58, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (82088060357293 / 100000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (557941890477 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12866_59 : CellCertificate 12866 (882110494979257 / 10000000000000000 : ℝ) (816273107407797 / 500000000000000000 : ℝ) (329665017950351 / 10000000000000000 : ℝ)
    (cell12866 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · norm_num [cell12866]
  · have h := gap_lower (n := 12866) (a := (4102726259203 / 5000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231771597201 / 100000000000000 : ℝ))
      (E := (cell12866 ⟨59, by decide⟩).energy) (xi := (329665017950351 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12866 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12866]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12866])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12866) (a := (4102726259203 / 5000000000000 : ℝ)) (b := (80035868731 / 50000000000000 : ℝ)) (q := (2231771597201 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12866])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12866]

theorem cert12867_40 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10336957672769 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (223157779209 / 10000000000000 : ℝ))
      (E := (cell12867 ⟨40, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10336957672769 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (223157779209 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_41 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82661707116283 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231581793147 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨41, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82661707116283 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231581793147 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_42 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82627776394127 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115792901259 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨42, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82627776394127 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115792901259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_43 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82593869186117 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (446317963829 / 20000000000000 : ℝ))
      (E := (cell12867 ⟨43, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82593869186117 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (446317963829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_44 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82559985462837 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231593841747 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨44, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82559985462837 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231593841747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_45 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82526125195017 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (223159786883 / 10000000000000 : ℝ))
      (E := (cell12867 ⟨45, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82526125195017 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (223159786883 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_46 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (16498457670707 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231601839779 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨46, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (16498457670707 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231601839779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_47 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10307309363677 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557901467613 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨47, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10307309363677 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557901467613 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_48 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20606171208457 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231609840881 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨48, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20606171208457 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231609840881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_49 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82390918098087 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557903466647 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨49, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82390918098087 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557903466647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_50 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82357174673649 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115808943041 / 50000000000000 : ℝ))
      (E := (cell12867 ⟨50, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82357174673649 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (1115808943041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_51 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (16464690906423 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557905474147 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨51, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (16464690906423 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557905474147 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_52 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (20572439411307 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557906473779 / 25000000000000 : ℝ))
      (E := (cell12867 ⟨52, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (20572439411307 / 25000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (557906473779 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_53 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (10282010498109 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (17434608887 / 781250000000 : ℝ))
      (E := (cell12867 ⟨53, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (10282010498109 / 12500000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (17434608887 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_54 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82222433523069 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231633902331 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨54, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82222433523069 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231633902331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_55 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (16437761246397 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231637904043 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨55, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (16437761246397 / 20000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231637904043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_56 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82155202083921 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (55791048473 / 2500000000000 : ℝ))
      (E := (cell12867 ⟨56, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82155202083921 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (55791048473 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_57 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82121621051317 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (13947787149 / 625000000000 : ℝ))
      (E := (cell12867 ⟨57, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82121621051317 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (13947787149 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_58 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (1282625986043 / 1562500000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231649973751 / 100000000000000 : ℝ))
      (E := (cell12867 ⟨58, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (1282625986043 / 1562500000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (2231649973751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12867_59 : CellCertificate 12867 (11026040598737 / 125000000000000 : ℝ) (1632419295097223 / 1000000000000000000 : ℝ) (329638788721569 / 10000000000000000 : ℝ)
    (cell12867 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · norm_num [cell12867]
  · have h := gap_lower (n := 12867) (a := (82054528222939 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139478372817 / 6250000000000 : ℝ))
      (E := (cell12867 ⟨59, by decide⟩).energy) (xi := (329638788721569 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12867 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12867]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12867])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12867) (a := (82054528222939 / 100000000000000 : ℝ)) (b := (160059149303 / 100000000000000 : ℝ)) (q := (139478372817 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12867])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12867]

theorem cert12868_40 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41347829427181 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223146021869 / 10000000000000 : ℝ))
      (E := (cell12868 ⟨40, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41347829427181 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223146021869 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_41 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41330852442563 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223146422287 / 10000000000000 : ℝ))
      (E := (cell12868 ⟨41, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41330852442563 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (223146422287 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_42 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41313887229597 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (44629364721 / 2000000000000 : ℝ))
      (E := (cell12868 ⟨42, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41313887229597 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (44629364721 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_43 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82593867547 / 100000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231472257169 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨43, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82593867547 / 100000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231472257169 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_44 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82559984119129 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231476226089 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨44, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82559984119129 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231476226089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_45 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82526124146311 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115740129503 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨45, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82526124146311 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115740129503 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_46 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41246143799713 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231484236471 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨46, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41246143799713 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231484236471 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_47 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82458474449499 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115744137171 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨47, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82458474449499 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115744137171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_48 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82424684667699 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278936531581 / 12500000000000 : ℝ))
      (E := (cell12868 ⟨48, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82424684667699 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278936531581 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_49 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82390918225341 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231496286913 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨49, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82390918225341 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231496286913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_50 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (20589293773471 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231500256647 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨50, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (20589293773471 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231500256647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_51 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82323455244929 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557876069261 / 25000000000000 : ℝ))
      (E := (cell12868 ⟨51, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82323455244929 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (557876069261 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_52 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (82289758650219 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115754143071 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨52, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (82289758650219 / 100000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115754143071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_53 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41128042640819 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115756140371 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨53, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41128042640819 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115756140371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_54 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (20555608777803 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231516316529 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨54, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (20555608777803 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231516316529 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_55 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (80262507921 / 97656250000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231520330841 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨55, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (80262507921 / 97656250000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231520330841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_56 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41077602126809 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115762159927 / 50000000000000 : ℝ))
      (E := (cell12868 ⟨56, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41077602126809 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (1115762159927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_57 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (41060811755597 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231528338699 / 100000000000000 : ℝ))
      (E := (cell12868 ⟨57, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (41060811755597 / 50000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (2231528338699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_58 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (20522016464103 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278941540503 / 12500000000000 : ℝ))
      (E := (cell12868 ⟨58, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (20522016464103 / 25000000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (278941540503 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12868_59 : CellCertificate 12868 (35282240195183 / 400000000000000 : ℝ) (816146197555831 / 500000000000000000 : ℝ) (6592251274221 / 200000000000000 : ℝ)
    (cell12868 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · norm_num [cell12868]
  · have h := gap_lower (n := 12868) (a := (2564204101937 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446307277961 / 20000000000000 : ℝ))
      (E := (cell12868 ⟨59, by decide⟩).energy) (xi := (6592251274221 / 200000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12868 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12868]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12868])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12868) (a := (2564204101937 / 3125000000000 : ℝ)) (b := (32009312627 / 20000000000000 : ℝ)) (q := (446307277961 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12868])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12868]

theorem cert12869_40 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82695656327401 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (278917830283 / 12500000000000 : ℝ))
      (E := (cell12869 ⟨40, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82695656327401 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (278917830283 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_41 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82661702654763 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231346649603 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨41, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82661702654763 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231346649603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_42 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (4131388626251 / 5000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231350666627 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨42, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (4131388626251 / 5000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231350666627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_43 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82593865908607 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (13945966459 / 625000000000 : ℝ))
      (E := (cell12869 ⟨43, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82593865908607 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (13945966459 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_44 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (8255998277611 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446271733281 / 20000000000000 : ℝ))
      (E := (cell12869 ⟨44, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (8255998277611 / 10000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (446271733281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_45 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82526123098259 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (34865041349 / 1562500000000 : ℝ))
      (E := (cell12869 ⟨45, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82526123098259 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (34865041349 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_46 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (5155767927871 / 6250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231366689257 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨46, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (5155767927871 / 6250000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231366689257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_47 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16491694798033 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115685337729 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨47, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16491694798033 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115685337729 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_48 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82424684502117 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231374720629 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨48, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82424684502117 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231374720629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_49 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (20597729588277 / 25000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231378704537 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨49, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (20597729588277 / 25000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231378704537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_50 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82357175514597 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231382683543 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨50, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82357175514597 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231382683543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_51 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (16464691191637 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557846678473 / 25000000000000 : ℝ))
      (E := (cell12869 ⟨51, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (16464691191637 / 20000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (557846678473 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_52 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41144879827809 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115695366809 / 50000000000000 : ℝ))
      (E := (cell12869 ⟨52, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41144879827809 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (1115695366809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_53 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41128043289389 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (89255789581 / 4000000000000 : ℝ))
      (E := (cell12869 ⟨53, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41128043289389 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (89255789581 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_54 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82222436699693 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231398728203 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨54, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82222436699693 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231398728203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_55 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82188809990527 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (44628055103 / 2000000000000 : ℝ))
      (E := (cell12869 ⟨55, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82188809990527 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (44628055103 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_56 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (2567350200737 / 3125000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231406757473 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨56, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (2567350200737 / 3125000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231406757473 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_57 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41060812985653 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231410790303 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨57, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41060812985653 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231410790303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_58 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (82088068606271 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231414790287 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨58, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (82088068606271 / 100000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231414790287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12869_59 : CellCertificate 12869 (17640575318403 / 200000000000000 : ℝ) (1632165514854307 / 1000000000000000000 : ℝ) (329586342917701 / 10000000000000000 : ℝ)
    (cell12869 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · norm_num [cell12869]
  · have h := gap_lower (n := 12869) (a := (41027267150597 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231418812191 / 100000000000000 : ℝ))
      (E := (cell12869 ⟨59, by decide⟩).energy) (xi := (329586342917701 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12869 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12869]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12869])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12869) (a := (41027267150597 / 50000000000000 : ℝ)) (b := (160033978957 / 100000000000000 : ℝ)) (q := (2231418812191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12869])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12869]

theorem cert12870_40 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82695653801271 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231225062811 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨40, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82695653801271 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231225062811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_41 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (16532340085039 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115614536673 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨41, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (16532340085039 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115614536673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_42 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (16525554118321 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231233094251 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨42, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (16525554118321 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231233094251 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_43 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41296932135469 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115618562231 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨43, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41296932135469 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115618562231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_44 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82559981433779 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231241103841 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨44, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82559981433779 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231241103841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_45 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82526122050861 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115622574291 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨45, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82526122050861 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115622574291 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_46 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (10311535761633 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115624569617 / 50000000000000 : ℝ))
      (E := (cell12870 ⟨46, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (10311535761633 / 12500000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (1115624569617 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_47 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41229236765707 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278906641591 / 12500000000000 : ℝ))
      (E := (cell12870 ⟨47, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41229236765707 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (278906641591 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_48 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82424684337083 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231257126921 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨48, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82424684337083 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231257126921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_49 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (20597729620347 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231261178433 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨49, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (20597729620347 / 25000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231261178433 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_50 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82357175935787 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557816291693 / 25000000000000 : ℝ))
      (E := (cell12870 ⟨50, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82357175935787 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557816291693 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_51 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (16464691334377 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231269148109 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨51, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (16464691334377 / 20000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231269148109 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_52 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (5143110041339 / 6250000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231273178501 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨52, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (5143110041339 / 6250000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231273178501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_53 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82256087876291 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (8925108783 / 400000000000 : ℝ))
      (E := (cell12870 ⟨53, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82256087876291 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (8925108783 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_54 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82222438288513 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446256239289 / 20000000000000 : ℝ))
      (E := (cell12870 ⟨54, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82222438288513 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (446256239289 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_55 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (41094405935127 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231285176971 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨55, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (41094405935127 / 50000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231285176971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_56 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82155208593819 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231289192641 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨56, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82155208593819 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231289192641 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_57 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82121628431651 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557823309873 / 25000000000000 : ℝ))
      (E := (cell12870 ⟨57, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82121628431651 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (557823309873 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_58 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82088071356329 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223129725417 / 10000000000000 : ℝ))
      (E := (cell12870 ⟨58, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82088071356329 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (223129725417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12870_59 : CellCertificate 12870 (441000765509867 / 5000000000000000 : ℝ) (20400483179007 / 12500000000000000 : ℝ) (20597507896277 / 625000000000000 : ℝ)
    (cell12870 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · norm_num [cell12870]
  · have h := gap_lower (n := 12870) (a := (82054537340569 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231301232231 / 100000000000000 : ℝ))
      (E := (cell12870 ⟨59, by decide⟩).energy) (xi := (20597507896277 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12870 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12870]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12870])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12870) (a := (82054537340569 / 100000000000000 : ℝ)) (b := (5000668649 / 3125000000000 : ℝ)) (q := (2231301232231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12870])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12870]

theorem cert12871_40 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (8269565127597 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (111555379893 / 5000000000000 : ℝ))
      (E := (cell12871 ⟨40, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (8269565127597 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (111555379893 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_41 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82661698196421 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231111552887 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨41, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82661698196421 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231111552887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_42 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82627768658949 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557778894433 / 25000000000000 : ℝ))
      (E := (cell12871 ⟨42, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82627768658949 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557778894433 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_43 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (10324232829249 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231119612567 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨43, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (10324232829249 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231119612567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_44 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (10319997511517 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231123597253 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨44, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (10319997511517 / 12500000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231123597253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_45 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16505224200823 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115563794551 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨45, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16505224200823 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115563794551 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_46 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82492285340809 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231131586403 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨46, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82492285340809 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231131586403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_47 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16491694614649 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231135646153 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨47, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16491694614649 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231135646153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_48 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82424684172597 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115569824189 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨48, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82424684172597 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115569824189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_49 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (4119545930509 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557785912407 / 25000000000000 : ℝ))
      (E := (cell12871 ⟨49, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (4119545930509 / 5000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (557785912407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_50 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (16471435271491 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446229529467 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨50, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (16471435271491 / 20000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446229529467 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_51 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41161728693013 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231151638719 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨51, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41161728693013 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231151638719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_52 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (41144880833819 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446231135967 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨52, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (41144880833819 / 50000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446231135967 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_53 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82256089174177 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278894956177 / 12500000000000 : ℝ))
      (E := (cell12871 ⟨53, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82256089174177 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278894956177 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_54 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (8222243987767 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115581831083 / 50000000000000 : ℝ))
      (E := (cell12871 ⟨54, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (8222243987767 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (1115581831083 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_55 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (20547203437571 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278895964317 / 12500000000000 : ℝ))
      (E := (cell12871 ⟨55, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (20547203437571 / 25000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278895964317 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_56 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82155210764323 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446234336899 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨56, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82155210764323 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446234336899 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_57 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (8212163089223 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278896960783 / 12500000000000 : ℝ))
      (E := (cell12871 ⟨57, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (8212163089223 / 10000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (278896960783 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_58 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82088074106587 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231179715671 / 100000000000000 : ℝ))
      (E := (cell12871 ⟨58, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82088074106587 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (2231179715671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12871_59 : CellCertificate 12871 (27561696880543 / 312500000000000 : ℝ) (1631911813505821 / 1000000000000000000 : ℝ) (41191739247269 / 1250000000000000 : ℝ)
    (cell12871 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · norm_num [cell12871]
  · have h := gap_lower (n := 12871) (a := (82054540380109 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446236741827 / 20000000000000 : ℝ))
      (E := (cell12871 ⟨59, by decide⟩).energy) (xi := (41191739247269 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12871 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12871]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12871])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12871) (a := (82054540380109 / 100000000000000 : ℝ)) (b := (160008816569 / 100000000000000 : ℝ)) (q := (446236741827 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12871])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12871]

theorem cert12872_40 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82695648751499 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230990071119 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨40, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82695648751499 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230990071119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_41 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (2066542399211 / 2500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115497044113 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨41, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (2066542399211 / 2500000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115497044113 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_42 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82627766727051 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230998117071 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨42, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82627766727051 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2230998117071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_43 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (8259386099777 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115501048877 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨43, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (8259386099777 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115501048877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_44 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82559978751181 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278875760973 / 12500000000000 : ℝ))
      (E := (cell12872 ⟨44, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82559978751181 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278875760973 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_45 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41263059979011 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231010085659 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨45, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41263059979011 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231010085659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_46 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (20623071147293 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231014148571 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨46, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (20623071147293 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231014148571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_47 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82458472615659 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115509048939 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨47, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82458472615659 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115509048939 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_48 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (41212342004329 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557755527037 / 25000000000000 : ℝ))
      (E := (cell12872 ⟨48, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (41212342004329 / 50000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (557755527037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_49 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16478183747897 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115513059061 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨49, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16478183747897 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115513059061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_50 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82357176779601 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231030125233 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨50, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82357176779601 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231030125233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_51 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (8232345810061 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231034185721 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨51, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (8232345810061 / 10000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231034185721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_52 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (4114488133713 / 5000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (89241527143 / 4000000000000 : ℝ))
      (E := (cell12872 ⟨52, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (4114488133713 / 5000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (89241527143 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_53 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16451218094487 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231042159593 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨53, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16451218094487 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231042159593 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_54 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16444488293433 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278880773057 / 12500000000000 : ℝ))
      (E := (cell12872 ⟨54, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16444488293433 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278880773057 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_55 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82188815630617 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (4462100381 / 200000000000 : ℝ))
      (E := (cell12872 ⟨55, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82188815630617 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (4462100381 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_56 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (16431042587019 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231054173899 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨56, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (16431042587019 / 20000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231054173899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_57 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (20530408338261 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231058189781 / 100000000000000 : ℝ))
      (E := (cell12872 ⟨57, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (20530408338261 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (2231058189781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_58 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (20522019214261 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115531116989 / 50000000000000 : ℝ))
      (E := (cell12872 ⟨58, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (20522019214261 / 25000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (1115531116989 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12872_59 : CellCertificate 12872 (7055576587137 / 80000000000000 : ℝ) (815892496202747 / 500000000000000000 : ℝ) (32950770582977 / 1000000000000000 : ℝ)
    (cell12872 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · norm_num [cell12872]
  · have h := gap_lower (n := 12872) (a := (82054543419813 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278883280363 / 12500000000000 : ℝ))
      (E := (cell12872 ⟨59, by decide⟩).energy) (xi := (32950770582977 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12872 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12872]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12872])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12872) (a := (82054543419813 / 100000000000000 : ℝ)) (b := (159996238359 / 100000000000000 : ℝ)) (q := (278883280363 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12872])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12872]

theorem cert12873_40 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82695646227857 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115436300059 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨40, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82695646227857 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115436300059 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_41 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41330846870627 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230876620577 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨41, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41330846870627 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230876620577 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_42 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82627764795913 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230880653457 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨42, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82627764795913 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230880653457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_43 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (8259385936227 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115442319431 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨43, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (8259385936227 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115442319431 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_44 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (16511995482183 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230888634293 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨44, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (16511995482183 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230888634293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_45 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82526118912581 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115446319127 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨45, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82526118912581 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115446319127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_46 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (10311535479769 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557724162257 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨46, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (10311535479769 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557724162257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_47 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (1288413627479 / 1562500000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115450332343 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨47, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (1288413627479 / 1562500000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115450332343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_48 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41212341922633 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446180936617 / 20000000000000 : ℝ))
      (E := (cell12873 ⟨48, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41212341922633 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (446180936617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_49 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82390918869301 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557727175467 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨49, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82390918869301 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557727175467 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_50 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82357177202223 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230912659467 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨50, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82357177202223 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230912659467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_51 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82323458815637 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230916671073 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨51, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82323458815637 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230916671073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_52 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (10286220460161 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557730168681 / 25000000000000 : ℝ))
      (E := (cell12873 ⟨52, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (10286220460161 / 12500000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (557730168681 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_53 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41128045885533 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115462363141 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨53, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41128045885533 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115462363141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_54 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (41111221528499 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (89237148169 / 4000000000000 : ℝ))
      (E := (cell12873 ⟨54, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (41111221528499 / 50000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (89237148169 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_55 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (20547204377813 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115466361547 / 50000000000000 : ℝ))
      (E := (cell12873 ⟨55, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (20547204377813 / 25000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (1115466361547 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_56 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (16431043021227 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278867089999 / 12500000000000 : ℝ))
      (E := (cell12873 ⟨56, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (16431043021227 / 20000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (278867089999 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_57 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (8212163581409 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230940750049 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨57, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (8212163581409 / 10000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230940750049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_58 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (820880796077 / 1000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230944749907 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨58, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (820880796077 / 1000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230944749907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12873_59 : CellCertificate 12873 (88191985066303 / 1000000000000000 : ℝ) (1631658191014981 / 1000000000000000000 : ℝ) (329481501894197 / 10000000000000000 : ℝ)
    (cell12873 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · norm_num [cell12873]
  · have h := gap_lower (n := 12873) (a := (82054546459683 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230948774329 / 100000000000000 : ℝ))
      (E := (cell12873 ⟨59, by decide⟩).energy) (xi := (329481501894197 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12873 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12873]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12873])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12873) (a := (82054546459683 / 100000000000000 : ℝ)) (b := (159983662137 / 100000000000000 : ℝ)) (q := (2230948774329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12873])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12873]

theorem cert12874_40 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20673910926261 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115377592429 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨40, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20673910926261 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115377592429 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_41 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41330845757431 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230759149939 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨41, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41330845757431 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230759149939 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_42 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20656940716383 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230763186893 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨42, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20656940716383 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230763186893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_43 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41296928863747 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230767177053 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨43, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41296928863747 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230767177053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_44 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (16511995214267 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557692794481 / 25000000000000 : ℝ))
      (E := (cell12874 ⟨44, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (16511995214267 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (557692794481 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_45 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82526117867793 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115387594003 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨45, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82526117867793 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115387594003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_46 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82492283087749 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230779205583 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨46, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82492283087749 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230779205583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_47 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41229235851117 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (89231329149 / 4000000000000 : ℝ))
      (E := (cell12874 ⟨47, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41229235851117 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (89231329149 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_48 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82424683682421 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (278848406911 / 12500000000000 : ℝ))
      (E := (cell12874 ⟨48, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82424683682421 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (278848406911 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_49 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (8239091899963 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115395611969 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨49, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (8239091899963 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115395611969 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_50 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (41178588812661 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446159050007 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨50, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (41178588812661 / 50000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446159050007 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_51 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (16464691906221 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230799271843 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨51, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (16464691906221 / 20000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230799271843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_52 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20572441172181 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230803286371 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨52, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20572441172181 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230803286371 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_53 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (8225609307007 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446161458083 / 20000000000000 : ℝ))
      (E := (cell12874 ⟨53, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (8225609307007 / 10000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (446161458083 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_54 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82222444647169 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115405640283 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨54, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82222444647169 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115405640283 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_55 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82188819392191 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230815312319 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨55, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82188819392191 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230815312319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_56 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20538804319361 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (89232772911 / 4000000000000 : ℝ))
      (E := (cell12874 ⟨56, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20538804319361 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (89232772911 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_57 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (82121638275371 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230823307901 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨57, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (82121638275371 / 100000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230823307901 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_58 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20522020589639 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115413661321 / 50000000000000 : ℝ))
      (E := (cell12874 ⟨58, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20522020589639 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (1115413661321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

theorem cert12874_59 : CellCertificate 12874 (881892631989141 / 10000000000000000 : ℝ) (163153140932969 / 100000000000000000 : ℝ) (41181912771293 / 1250000000000000 : ℝ)
    (cell12874 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · norm_num [cell12874]
  · have h := gap_lower (n := 12874) (a := (20513637374929 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230831303411 / 100000000000000 : ℝ))
      (E := (cell12874 ⟨59, by decide⟩).energy) (xi := (41181912771293 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12874 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12874]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12874])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12874) (a := (20513637374929 / 25000000000000 : ℝ)) (b := (159971087903 / 100000000000000 : ℝ)) (q := (2230831303411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12874])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12874]

end BstLean.Part268
