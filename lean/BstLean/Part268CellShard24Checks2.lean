import BstLean.Part268CellShard24Checks1

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12950_40 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (2067386359463 / 2500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110953291417 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨40, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (2067386359463 / 2500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110953291417 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_41 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41330762306559 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222191059347 / 10000000000000 : ℝ))
      (E := (cell12950 ⟨41, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41330762306559 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222191059347 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_42 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (1032845229471 / 1250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110957304967 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨42, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (1032845229471 / 1250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110957304967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_43 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82593735582703 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110959315517 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨43, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82593735582703 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110959315517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_44 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (8255987625883 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221922655363 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨44, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (8255987625883 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221922655363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_45 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20631510089213 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222192662241 / 10000000000000 : ℝ))
      (E := (cell12950 ⟨45, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20631510089213 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222192662241 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_46 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82492227847707 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222193064809 / 10000000000000 : ℝ))
      (E := (cell12950 ⟨46, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82492227847707 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (222193064809 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_47 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (1030730483781 / 1250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444386934297 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨47, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (1030730483781 / 1250000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444386934297 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_48 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82424672892399 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221938690327 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨48, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82424672892399 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221938690327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_49 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20597732597209 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221942702139 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨49, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20597732597209 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221942702139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_50 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20589302790827 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221946704229 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨50, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20589302790827 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221946704229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_51 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82323515187473 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444390138739 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨51, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82323515187473 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444390138739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_52 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20572460608283 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110977363237 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨52, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20572460608283 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110977363237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_53 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (3290247714889 / 4000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (27774484253 / 1250000000000 : ℝ))
      (E := (cell12950 ⟨53, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (3290247714889 / 4000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (27774484253 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_54 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41111283238417 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221962731461 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨54, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41111283238417 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221962731461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_55 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41094481609589 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221966755519 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨55, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41094481609589 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221966755519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_56 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (641838930247 / 781250000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221970749391 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨56, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (641838930247 / 781250000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221970749391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_57 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20530456501661 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555493692023 / 25000000000000 : ℝ))
      (E := (cell12950 ⟨57, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20530456501661 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555493692023 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_58 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (2565259124903 / 3125000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (111098937407 / 5000000000000 : ℝ))
      (E := (cell12950 ⟨58, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (2565259124903 / 3125000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (111098937407 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_59 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (82054781015139 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221982803403 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨59, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (82054781015139 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221982803403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12951_40 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (16539090383763 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221791170387 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨40, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (16539090383763 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221791170387 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_41 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (661292179577 / 800000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221795188099 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨41, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (661292179577 / 800000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221795188099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_42 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20656904121249 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221799153499 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨42, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20656904121249 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221799153499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_43 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82593734002923 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221803183011 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨43, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82593734002923 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221803183011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_44 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82559874971551 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222180721643 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨44, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82559874971551 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222180721643 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_45 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (10315754920209 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221811193247 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨45, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (10315754920209 / 12500000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221811193247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_46 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (3299689085769 / 4000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221815229373 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨46, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (3299689085769 / 4000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221815229373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_47 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (16491687658059 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444363840991 / 20000000000000 : ℝ))
      (E := (cell12951 ⟨47, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (16491687658059 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444363840991 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_48 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (8242467277111 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110911617787 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨48, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (8242467277111 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110911617787 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_49 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20597732639511 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110913629919 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨49, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20597732639511 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110913629919 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_50 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (16471442324523 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110915637527 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨50, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (16471442324523 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110915637527 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_51 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82323515936481 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (27772940979 / 1250000000000 : ℝ))
      (E := (cell12951 ⟨51, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82323515936481 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (27772940979 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_52 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82289843471443 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110919633261 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨52, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82289843471443 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110919633261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_53 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82256194199443 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555460823853 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨53, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82256194199443 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555460823853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_54 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41111284046281 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222184730243 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨54, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41111284046281 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222184730243 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_55 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41094482561511 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (277731410479 / 12500000000000 : ℝ))
      (E := (cell12951 ⟨55, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41094482561511 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (277731410479 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_56 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (82155385263181 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (111092764741 / 5000000000000 : ℝ))
      (E := (cell12951 ⟨56, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (82155385263181 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (111092764741 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_57 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (2566307140173 / 3125000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221859331307 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨57, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (2566307140173 / 3125000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221859331307 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_58 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41044147381361 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222186332981 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨58, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41044147381361 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222186332981 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_59 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41027392033753 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221867344981 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨59, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41027392033753 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221867344981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12952_40 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (1033693118249 / 1250000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221675754981 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨40, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (1033693118249 / 1250000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221675754981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_41 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20665380070477 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138854982563 / 6250000000000 : ℝ))
      (E := (cell12952 ⟨41, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20665380070477 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138854982563 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_42 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82627614613051 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444336750599 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨42, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82627614613051 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444336750599 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_43 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (10324216552981 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444337546427 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨43, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (10324216552981 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444337546427 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_44 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82559873684943 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221691774681 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨44, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82559873684943 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221691774681 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_45 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82526038367129 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221695761301 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨45, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82526038367129 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221695761301 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_46 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (16498445288269 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555424951977 / 25000000000000 : ℝ))
      (E := (cell12952 ⟨46, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (16498445288269 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555424951977 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_47 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20614609469669 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (44434075893 / 2000000000000 : ℝ))
      (E := (cell12952 ⟨47, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20614609469669 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (44434075893 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_48 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41212336325177 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444341555629 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨48, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41212336325177 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444341555629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_49 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82390930727751 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138856988431 / 6250000000000 : ℝ))
      (E := (cell12952 ⟨49, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82390930727751 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138856988431 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_50 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41178606041193 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110857921637 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨50, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41178606041193 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110857921637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_51 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41161758342959 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221719860377 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨51, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41161758342959 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221719860377 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_52 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82289844510149 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138857741443 / 6250000000000 : ℝ))
      (E := (cell12952 ⟨52, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82289844510149 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (138857741443 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_53 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82256195527021 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444345569617 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨53, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82256195527021 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444345569617 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_54 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82222569708617 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221731870933 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨54, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82222569708617 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221731870933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_55 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41094483513579 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221735868839 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨55, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41094483513579 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221735868839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_56 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20538846863751 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221739897 / 100000000000 : ℝ))
      (E := (cell12952 ⟨56, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20538846863751 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221739897 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_57 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20530457741163 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110871946081 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨57, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20530457741163 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110871946081 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_58 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82088297528737 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555436977289 / 25000000000000 : ℝ))
      (E := (cell12952 ⟨58, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82088297528737 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (555436977289 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_59 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (82054787120029 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (222175188427 / 10000000000000 : ℝ))
      (E := (cell12952 ⟨59, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (82054787120029 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (222175188427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12953_40 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16539089400367 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277695042077 / 12500000000000 : ℝ))
      (E := (cell12953 ⟨40, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16539089400367 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277695042077 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_41 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41330759058733 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277695546073 / 12500000000000 : ℝ))
      (E := (cell12953 ⟨41, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41330759058733 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277695546073 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_42 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (10328451592731 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110784174801 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨42, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (10328451592731 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110784174801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_43 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82593730845479 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221572337249 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨43, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82593730845479 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221572337249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_44 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41279936199503 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221576388979 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨44, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41279936199503 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221576388979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_45 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82526037373221 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221580385463 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨45, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82526037373221 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221580385463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_46 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41246112869533 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221584383699 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨46, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41246112869533 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221584383699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_47 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (659667499741 / 800000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444317676327 / 20000000000000 : ℝ))
      (E := (cell12953 ⟨47, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (659667499741 / 800000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444317676327 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_48 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (8242467253013 / 10000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221592377001 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨48, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (8242467253013 / 10000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221592377001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_49 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (20597732724489 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221596426297 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨49, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (20597732724489 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221596426297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_50 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (4117860627131 / 5000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221600408891 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨50, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (4117860627131 / 5000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221600408891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_51 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (10290439679473 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277700554983 / 12500000000000 : ℝ))
      (E := (cell12953 ⟨51, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (10290439679473 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277700554983 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_52 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (329159382197 / 400000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (13885052857 / 625000000000 : ℝ))
      (E := (cell12953 ⟨52, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (329159382197 / 400000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (13885052857 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_53 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (1028202460687 / 1250000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110806228667 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨53, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (1028202460687 / 1250000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110806228667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_54 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82222571324999 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555404109243 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨54, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82222571324999 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555404109243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_55 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82188968931587 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277702556427 / 12500000000000 : ℝ))
      (E := (cell12953 ⟨55, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82188968931587 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277702556427 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_56 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16431077929417 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221624496787 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨56, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16431077929417 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221624496787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_57 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (10265229180499 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555407127457 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨57, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (10265229180499 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555407127457 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_58 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (82088300294943 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221632486177 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨58, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (82088300294943 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221632486177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_59 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (20513697543177 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110818269851 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨59, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (20513697543177 / 25000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110818269851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12954_40 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1033693056807 / 1250000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110722487031 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨40, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1033693056807 / 1250000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110722487031 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_41 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41330757976899 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110724477221 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨41, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41330757976899 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110724477221 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_42 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (10328451358923 / 12500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (111072650107 / 5000000000000 : ℝ))
      (E := (cell12954 ⟨42, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (10328451358923 / 12500000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (111072650107 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_43 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (16518745853563 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (138841062397 / 6250000000000 : ℝ))
      (E := (cell12954 ⟨43, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (16518745853563 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (138841062397 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_44 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82559871113739 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110730500231 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨44, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82559871113739 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110730500231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_45 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1650520727599 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221465006843 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨45, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1650520727599 / 2000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221465006843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_46 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (20623056259347 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (277683626957 / 12500000000000 : ℝ))
      (E := (cell12954 ⟨46, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (20623056259347 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (277683626957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_47 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (4122921852857 / 5000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444294604969 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨47, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (4122921852857 / 5000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444294604969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_48 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41212336205219 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (111073851607 / 5000000000000 : ℝ))
      (E := (cell12954 ⟨48, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41212336205219 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (111073851607 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_49 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41195465534329 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110740517529 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨49, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41195465534329 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110740517529 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_50 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41178606501659 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221485030907 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨50, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41178606501659 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221485030907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_51 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82323518186079 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221489075811 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨51, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82323518186079 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221489075811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_52 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (16457969317749 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110746524309 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨52, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (16457969317749 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110746524309 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_53 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (4112809909163 / 5000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555374266021 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨53, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (4112809909163 / 5000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555374266021 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_54 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41111286470853 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221501059647 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨54, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41111286470853 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221501059647 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_55 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (82188970836307 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (17355508521 / 781250000000 : ℝ))
      (E := (cell12954 ⟨55, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (82188970836307 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (17355508521 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_56 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (1283677997491 / 1562500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221509094179 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨56, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (1283677997491 / 1562500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221509094179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_57 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (20530458980889 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110756562567 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨57, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (20530458980889 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110756562567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_58 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41044151530669 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221517120067 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨58, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41044151530669 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221517120067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_59 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41027396612771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555380283407 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨59, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41027396612771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555380283407 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12955_40 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16539088417619 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221329608551 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨40, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16539088417619 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221329608551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_41 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41330756895453 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221333596171 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨41, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41330756895453 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221333596171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_42 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (4131380450083 / 5000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221337651791 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨42, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (4131380450083 / 5000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221337651791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_43 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82593727690857 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221341656603 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨43, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82593727690857 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221341656603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_44 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82559869829143 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221345667993 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨44, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82559869829143 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221345667993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_45 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41263017693657 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555337406361 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨45, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41263017693657 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555337406361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_46 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82492224336311 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221353644869 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨46, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82492224336311 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221353644869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_47 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41229218323611 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444271533069 / 20000000000000 : ℝ))
      (E := (cell12955 ⟨47, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41229218323611 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444271533069 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_48 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82424672291279 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555340421151 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨48, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82424672291279 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555340421151 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_49 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82390931239857 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221365700163 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨49, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82390931239857 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221365700163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_50 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41178606732239 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221369709327 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨50, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41178606732239 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221369709327 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_51 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82323518936803 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221373709189 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨51, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82323518936803 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221373709189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_52 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16457969525727 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110688848317 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨52, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16457969525727 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110688848317 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_53 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82256199511919 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555345431853 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨53, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82256199511919 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555345431853 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_54 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82222574558739 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221385738959 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨54, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82222574558739 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221385738959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_55 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82188972741319 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221389727531 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨55, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82188972741319 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221389727531 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_56 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (4107769701601 / 5000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (88855749933 / 4000000000000 : ℝ))
      (E := (cell12955 ⟨56, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (4107769701601 / 5000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (88855749933 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_57 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82121838403343 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110698869041 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨57, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82121838403343 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110698869041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_58 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (82088305827923 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221401751633 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨58, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (82088305827923 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221401751633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_59 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (20513699069633 / 25000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110702892241 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨59, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (20513699069633 / 25000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110702892241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12956_40 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41347719816219 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444242859771 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨40, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41347719816219 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444242859771 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_41 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (20665377907197 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (88848731751 / 4000000000000 : ℝ))
      (E := (cell12956 ⟨41, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (20665377907197 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (88848731751 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_42 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (20656901783169 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221222298557 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨42, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (20656901783169 / 25000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221222298557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_43 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82593726114603 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110613156003 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨43, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82593726114603 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110613156003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_44 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82559868545217 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222123033271 / 10000000000000 : ℝ))
      (E := (cell12956 ⟨44, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82559868545217 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222123033271 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_45 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82526034395313 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444246860031 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨45, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82526034395313 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444246860031 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_46 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16498444727167 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (8884953321 / 400000000000 : ℝ))
      (E := (cell12956 ⟨46, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16498444727167 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (8884953321 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_47 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (8245843623787 / 10000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221242362073 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨47, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (8245843623787 / 10000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221242362073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_48 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82424672172651 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555311583599 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨48, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82424672172651 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555311583599 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_49 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41195465705777 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221250362631 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨49, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41195465705777 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221250362631 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_50 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41178606963051 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221254385143 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨50, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41178606963051 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221254385143 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_51 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16464703937591 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222125839903 / 10000000000000 : ℝ))
      (E := (cell12956 ⟨51, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16464703937591 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (222125839903 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_52 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82289848668919 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555315600293 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨52, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82289848668919 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555315600293 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_53 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41128100420469 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555316597061 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨53, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41128100420469 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555316597061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_54 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41111288088049 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221270415809 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨54, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41111288088049 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221270415809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_55 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41094487323311 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221274421071 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨55, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41094487323311 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221274421071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_56 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41077698112437 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (88851138369 / 4000000000000 : ℝ))
      (E := (cell12956 ⟨56, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41077698112437 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (88851138369 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_57 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82121840883353 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221282467013 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨57, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82121840883353 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221282467013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_58 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82088308594697 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221286440071 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨58, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82088308594697 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221286440071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_59 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (82054799331677 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277661304131 / 12500000000000 : ℝ))
      (E := (cell12956 ⟨59, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (82054799331677 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277661304131 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12957_40 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82695437177591 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110549493101 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨40, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82695437177591 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110549493101 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_41 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20665377366861 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110551494229 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨41, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20665377366861 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110551494229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_42 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82627605264431 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (277638375157 / 12500000000000 : ℝ))
      (E := (cell12957 ⟨42, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82627605264431 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (277638375157 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_43 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82593724539053 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221111023401 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨43, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82593724539053 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221111023401 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_44 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82559867261961 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221114994613 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨44, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82559867261961 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221114994613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_45 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20631508350987 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (34704984859 / 1562500000000 : ℝ))
      (E := (cell12957 ⟨45, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20631508350987 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (34704984859 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_46 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (2062305573399 / 2500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221123012887 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨46, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (2062305573399 / 2500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221123012887 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_47 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20614608957271 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110563528047 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨47, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20614608957271 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110563528047 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_48 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41212336027277 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (555282760119 / 25000000000000 : ℝ))
      (E := (cell12957 ⟨48, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41212336027277 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (555282760119 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_49 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82390931583749 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221135081443 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨49, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82390931583749 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221135081443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_50 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20589303597047 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221139058359 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨50, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20589303597047 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221139058359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_51 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (5145220027471 / 6250000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69410721447 / 3125000000000 : ℝ))
      (E := (cell12957 ⟨51, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (5145220027471 / 6250000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69410721447 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_52 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82289849709597 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110573551589 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨52, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82289849709597 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110573551589 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_53 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82256202170317 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444230221131 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨53, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82256202170317 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444230221131 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_54 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41111288896891 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110577545099 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨54, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41111288896891 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110577545099 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_55 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82188976552217 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (277644889023 / 12500000000000 : ℝ))
      (E := (cell12957 ⟨55, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82188976552217 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (277644889023 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_56 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (16431079683597 / 20000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221163108587 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨56, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (16431079683597 / 20000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221163108587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_57 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (82121843363587 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221167134417 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨57, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (82121843363587 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221167134417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_58 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (4104415568083 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221171126187 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨58, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (4104415568083 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2221171126187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_59 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41027401192489 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (138823446159 / 6250000000000 : ℝ))
      (E := (cell12957 ⟨59, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41027401192489 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (138823446159 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12958_40 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82695434723553 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444196745873 / 20000000000000 : ℝ))
      (E := (cell12958 ⟨40, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82695434723553 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444196745873 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_41 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41330753653437 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277623467377 / 12500000000000 : ℝ))
      (E := (cell12958 ⟨41, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41330753653437 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277623467377 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_42 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (3305104135877 / 4000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220991701071 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨42, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (3305104135877 / 4000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220991701071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_43 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82593722964209 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110497865973 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨43, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82593722964209 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110497865973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_44 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41279932989687 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (222099971257 / 10000000000000 : ℝ))
      (E := (cell12958 ⟨44, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41279932989687 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (222099971257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_45 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41263016206609 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221003759019 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨45, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41263016206609 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221003759019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_46 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16498444447337 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138812984481 / 6250000000000 : ℝ))
      (E := (cell12958 ⟨46, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16498444447337 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138812984481 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_47 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (1288413053451 / 1562500000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138813234213 / 6250000000000 : ℝ))
      (E := (cell12958 ⟨47, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (1288413053451 / 1562500000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (138813234213 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_48 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82424671936989 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221015802843 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨48, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82424671936989 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221015802843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_49 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (2059773293911 / 2500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (111050989881 / 5000000000000 : ℝ))
      (E := (cell12958 ⟨49, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (2059773293911 / 2500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (111050989881 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_50 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82357214850737 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221023787979 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨50, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82357214850737 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221023787979 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_51 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (10290440148943 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221027830043 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨51, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (10290440148943 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221027830043 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_52 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82289850750669 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110515901327 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨52, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82289850750669 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110515901327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_53 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (10282025437507 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221035820571 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨53, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (10282025437507 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221035820571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_54 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (5138911213237 / 6250000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88841592849 / 4000000000000 : ℝ))
      (E := (cell12958 ⟨54, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (5138911213237 / 6250000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88841592849 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_55 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (10273622307263 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110521929997 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨55, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (10273622307263 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110521929997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_56 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41077700305677 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221047873851 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨56, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41077700305677 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221047873851 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_57 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (20530461461011 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444210371727 / 20000000000000 : ℝ))
      (E := (cell12958 ⟨57, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (20530461461011 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444210371727 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_58 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (82088314128813 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110527934587 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨58, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (82088314128813 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110527934587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_59 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41027402719217 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221059900971 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨59, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41027402719217 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2221059900971 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12959_40 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82695432270323 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220868469573 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨40, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82695432270323 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220868469573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_41 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82661505147077 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (444174497331 / 20000000000000 : ℝ))
      (E := (cell12959 ⟨41, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82661505147077 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (444174497331 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_42 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41313800765079 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220876456821 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨42, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41313800765079 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220876456821 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_43 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20648430347517 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110440248243 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨43, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20648430347517 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110440248243 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_44 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82559864697457 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110442243289 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨44, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82559864697457 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110442243289 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_45 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82526031423123 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555222121071 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨45, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82526031423123 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555222121071 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_46 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (8249222153801 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110446243881 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨46, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (8249222153801 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110446243881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_47 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (8245843501321 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (44417929899 / 2000000000000 : ℝ))
      (E := (cell12959 ⟨47, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (8245843501321 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (44417929899 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_48 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (16484934363991 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220900503579 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨48, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (16484934363991 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220900503579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_49 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82390931929627 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220904511161 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨49, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82390931929627 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220904511161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_50 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20589303828437 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110454257499 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨50, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20589303828437 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110454257499 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_51 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82323521943981 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110456285607 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨51, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82323521943981 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110456285607 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_52 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41144925896067 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220916558653 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨52, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41144925896067 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220916558653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_53 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41128102415077 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220920592067 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨53, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41128102415077 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220920592067 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_54 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (5138911314383 / 6250000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220924608891 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨54, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (5138911314383 / 6250000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220924608891 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_55 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82188980364281 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220928605379 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨55, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82188980364281 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220928605379 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_56 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (82155402804979 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110466288789 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨56, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (82155402804979 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110466288789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_57 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (20530462081181 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220936639667 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨57, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (20530462081181 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220936639667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_58 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41044158448077 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110470304921 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨58, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41044158448077 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110470304921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_59 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (16410961698409 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220944661111 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨59, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (16410961698409 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220944661111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12960_40 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41347714908951 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555188301707 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨40, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41347714908951 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555188301707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_41 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41330751494027 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110378615689 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨41, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41330751494027 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110378615689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_42 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (8262759966413 / 10000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555190317127 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨42, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (8262759966413 / 10000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555190317127 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_43 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82593719816631 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (111038262909 / 5000000000000 : ℝ))
      (E := (cell12960 ⟨43, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82593719816631 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (111038262909 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_44 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82559863416209 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (138798078611 / 6250000000000 : ℝ))
      (E := (cell12960 ⟨44, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82559863416209 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (138798078611 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_45 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41263015216831 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444154653133 / 20000000000000 : ℝ))
      (E := (cell12960 ⟨45, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41263015216831 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444154653133 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_46 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (40279404707 / 48828125000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220777280001 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨46, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (40279404707 / 48828125000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220777280001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_47 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82458434606121 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88831251949 / 4000000000000 : ℝ))
      (E := (cell12960 ⟨47, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82458434606121 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88831251949 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_48 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82424671703453 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555196329891 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨48, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82424671703453 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555196329891 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_49 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (5149433256457 / 6250000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (44415785621 / 2000000000000 : ℝ))
      (E := (cell12960 ⟨49, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (5149433256457 / 6250000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (44415785621 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_50 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82357215777221 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110396649213 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨50, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82357215777221 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110396649213 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_51 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41161761348423 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220797309823 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨51, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41161761348423 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220797309823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_52 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41144926416997 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110400656061 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨52, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41144926416997 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110400656061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_53 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20564051540153 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (222080536107 / 10000000000000 : ℝ))
      (E := (cell12960 ⟨53, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20564051540153 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (222080536107 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_54 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20555645662197 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444161867 / 20000000000 : ℝ))
      (E := (cell12960 ⟨54, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20555645662197 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444161867 / 20000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_55 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (328755929083 / 400000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220813348341 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨55, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (328755929083 / 400000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220813348341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_56 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41077702499431 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220817397209 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨56, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41077702499431 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220817397209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_57 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82121850805627 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88832854367 / 4000000000000 : ℝ))
      (E := (cell12960 ⟨57, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82121850805627 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (88832854367 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_58 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (16417663932737 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220825407383 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨58, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (16417663932737 / 20000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220825407383 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_59 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (82054811545811 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220829418967 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨59, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (82054811545811 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220829418967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12961_40 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (5168464210393 / 6250000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110318999951 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨40, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (5168464210393 / 6250000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110318999951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_41 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (16532300165961 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (277580253997 / 12500000000000 : ℝ))
      (E := (cell12961 ⟨41, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (16532300165961 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (277580253997 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_42 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (2065689944971 / 2500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110323009247 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨42, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (2065689944971 / 2500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110323009247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_43 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41296859121949 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220650075869 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨43, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41296859121949 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220650075869 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_44 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (8255986213563 / 10000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555163521257 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨44, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (8255986213563 / 10000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555163521257 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_45 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (20631507361209 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555164511067 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨45, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (20631507361209 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555164511067 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_46 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82492220142461 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220662069499 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨46, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82492220142461 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220662069499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_47 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82458434199597 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444133219959 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨47, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82458434199597 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444133219959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_48 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82424671587481 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220670073921 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨48, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82424671587481 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220670073921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_49 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82390932277493 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220674107287 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨49, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82390932277493 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220674107287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_50 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82357216241157 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220678138259 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨50, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82357216241157 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220678138259 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_51 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41161761725069 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220682104897 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨51, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41161761725069 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220682104897 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_52 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41144926938123 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444137224423 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨52, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41144926938123 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444137224423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_53 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82256207491429 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110345063789 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨53, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82256207491429 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110345063789 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_54 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41111292133887 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138793386053 / 6250000000000 : ℝ))
      (E := (cell12961 ⟨54, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41111292133887 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138793386053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_55 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82188984177509 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220698148001 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨55, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82188984177509 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220698148001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_56 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82155407193001 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444140431061 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨56, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82155407193001 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444140431061 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_57 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (82121853286753 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220706194669 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨57, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (82121853286753 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220706194669 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_58 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (20522080607851 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444142040521 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨58, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (20522080607851 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444142040521 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_59 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (20513703649933 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220714174537 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨59, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (20513703649933 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220714174537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12962_40 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82695424915483 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555130712199 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨40, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82695424915483 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555130712199 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_41 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (10332687334041 / 12500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111026341483 / 5000000000000 : ℝ))
      (E := (cell12962 ⟨41, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (10332687334041 / 12500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111026341483 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_42 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82627595934289 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220530883237 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨42, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82627595934289 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220530883237 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_43 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82593716671869 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110267445357 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨43, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82593716671869 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110267445357 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_44 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82559860855721 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444107770121 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨44, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82559860855721 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444107770121 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_45 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20631507114161 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555135719747 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨45, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20631507114161 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555135719747 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_46 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41246109722793 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555136728793 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨46, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41246109722793 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555136728793 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_47 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82458433793639 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220550898161 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨47, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82458433793639 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220550898161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_48 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (2060616786801 / 2500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220554884569 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨48, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (2060616786801 / 2500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220554884569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_49 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (8239093245217 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220558930893 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨49, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (8239093245217 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220558930893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_50 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41178608352777 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222056291649 / 10000000000000 : ℝ))
      (E := (cell12962 ⟨50, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41178608352777 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222056291649 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_51 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82323524203859 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110283478219 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨51, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82323524203859 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110283478219 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_52 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20572463729723 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110285464791 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨52, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20572463729723 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110285464791 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_53 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (16451241764521 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138785934417 / 6250000000000 : ℝ))
      (E := (cell12962 ⟨53, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (16451241764521 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138785934417 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_54 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20555646471771 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220578957141 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨54, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20555646471771 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220578957141 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_55 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (1027362326057 / 1250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220583004363 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨55, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (1027362326057 / 1250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220583004363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_56 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82155409387397 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220586970161 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨56, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82155409387397 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220586970161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_57 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (82121855768101 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555147756953 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨57, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (82121855768101 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555147756953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_58 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (5130520324957 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220594995509 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨58, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (5130520324957 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220594995509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_59 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (5128426103363 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111029952313 / 5000000000000 : ℝ))
      (E := (cell12962 ⟨59, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (5128426103363 / 6250000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111029952313 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12963_40 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16539084493097 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110203847369 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨40, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16539084493097 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110203847369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_41 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (5290335777 / 6400000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110205841611 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨41, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (5290335777 / 6400000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110205841611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_42 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (20656898517619 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55510392157 / 2500000000000 : ℝ))
      (E := (cell12963 ⟨42, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (20656898517619 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55510392157 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_43 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82593715100543 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220419702713 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨43, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82593715100543 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220419702713 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_44 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82559859576479 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444084746221 / 20000000000000 : ℝ))
      (E := (cell12963 ⟨44, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82559859576479 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444084746221 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_45 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41263013734543 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220427710933 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨45, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41263013734543 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220427710933 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_46 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82492218749311 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444086351621 / 20000000000000 : ℝ))
      (E := (cell12963 ⟨46, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82492218749311 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444086351621 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_47 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16491686677649 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55510893819 / 2500000000000 : ℝ))
      (E := (cell12963 ⟨47, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16491686677649 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (55510893819 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_48 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82424671357129 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220439751509 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨48, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82424671357129 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220439751509 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_49 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82390932627343 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444088750373 / 20000000000000 : ℝ))
      (E := (cell12963 ⟨49, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82390932627343 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444088750373 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_50 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82357217170413 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277555968891 / 12500000000000 : ℝ))
      (E := (cell12963 ⟨50, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82357217170413 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277555968891 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_51 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41161762479003 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220451805417 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨51, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41161762479003 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220451805417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_52 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (20572463990483 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220455793573 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨52, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (20572463990483 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220455793573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_53 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82256210154139 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (44409196607 / 2000000000000 : ℝ))
      (E := (cell12963 ⟨53, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82256210154139 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (44409196607 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_54 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82222587506719 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555115948519 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨54, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82222587506719 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555115948519 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_55 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (821889879919 / 1000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220467799179 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨55, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (821889879919 / 1000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220467799179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_56 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (1643108231641 / 2000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (88818873671 / 4000000000000 : ℝ))
      (E := (cell12963 ⟨56, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (1643108231641 / 2000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (88818873671 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_57 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (10265232281209 / 12500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220475858601 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨57, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (10265232281209 / 12500000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220475858601 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_58 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (82088327967409 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277559980661 / 12500000000000 : ℝ))
      (E := (cell12963 ⟨58, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (82088327967409 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (277559980661 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_59 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41027410354019 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110241928241 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨59, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41027410354019 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110241928241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12964_40 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (16539084003259 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (17346035451 / 781250000000 : ℝ))
      (E := (cell12964 ⟨40, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (16539084003259 / 20000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (17346035451 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_41 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41330747179847 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277537074083 / 12500000000000 : ℝ))
      (E := (cell12964 ⟨41, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41330747179847 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277537074083 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_42 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (413137961037 / 500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110150302041 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨42, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (413137961037 / 500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110150302041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_43 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (258105354781 / 312500000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222030457071 / 10000000000000 : ℝ))
      (E := (cell12964 ⟨43, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (258105354781 / 312500000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (222030457071 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_44 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82559858297907 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110154304397 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨44, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82559858297907 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110154304397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_45 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41263013241081 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220312598993 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨45, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41263013241081 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220312598993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_46 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41246109026817 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110158299151 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨46, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41246109026817 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110158299151 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_47 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82458432983417 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (138770037791 / 6250000000000 : ℝ))
      (E := (cell12964 ⟨47, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82458432983417 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (138770037791 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_48 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82424671242749 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (111016230789 / 5000000000000 : ℝ))
      (E := (cell12964 ⟨48, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82424671242749 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (111016230789 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_49 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (20597733200753 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555082157297 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨49, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (20597733200753 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555082157297 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_50 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82357217635733 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (17346348767 / 781250000000 : ℝ))
      (E := (cell12964 ⟨50, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82357217635733 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (17346348767 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_51 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82323525712581 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220336651833 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨51, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82323525712581 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220336651833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_52 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (20572464251341 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110170327519 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨52, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (20572464251341 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110170327519 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_53 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82256211486033 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110172324229 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨53, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82256211486033 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110172324229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_54 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82222589126679 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220348687653 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨54, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82222589126679 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220348687653 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_55 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (20547247474883 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220352709819 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨55, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (20547247474883 / 25000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220352709819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_56 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82155413776959 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110178355501 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨56, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82155413776959 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110178355501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_57 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41060930365733 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220360746207 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨57, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41060930365733 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220360746207 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_58 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41044165367847 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277545593993 / 12500000000000 : ℝ))
      (E := (cell12964 ⟨58, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41044165367847 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277545593993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_59 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (82054823762423 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220368723637 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨59, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (82054823762423 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220368723637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12965_40 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82695417567911 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220177436543 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨40, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82695417567911 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220177436543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_41 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16532298440907 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110090720199 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨41, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16532298440907 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110090720199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_42 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41313795172531 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220185460187 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨42, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41313795172531 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220185460187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_43 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (2064842799 / 2500000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220189494707 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨43, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (2064842799 / 2500000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220189494707 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_44 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41279928510001 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110096741839 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨44, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41279928510001 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110096741839 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_45 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (1289469148373 / 1562500000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220197484283 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨45, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (1289469148373 / 1562500000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220197484283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_46 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82492217358557 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110100747337 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨46, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82492217358557 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110100747337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_47 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82458432579153 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220205512787 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨47, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82458432579153 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220205512787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_48 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41212335564449 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220209536347 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨48, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41212335564449 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220209536347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_49 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82390932979177 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (55505337597 / 2500000000000 : ℝ))
      (E := (cell12965 ⟨49, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82390932979177 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (55505337597 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_50 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16471443620303 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220217530629 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨50, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16471443620303 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220217530629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_51 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41161763233791 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220221554721 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨51, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41161763233791 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220221554721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_52 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82289858049189 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277528196629 / 12500000000000 : ℝ))
      (E := (cell12965 ⟨52, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82289858049189 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277528196629 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_53 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16451242563657 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220229582231 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨53, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16451242563657 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220229582231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_54 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20555647686741 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (88809343151 / 4000000000000 : ℝ))
      (E := (cell12965 ⟨54, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20555647686741 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (88809343151 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_55 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41094495903727 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (55505940451 / 2500000000000 : ℝ))
      (E := (cell12965 ⟨55, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41094495903727 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (55505940451 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_56 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20538853993031 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (555060394461 / 25000000000000 : ℝ))
      (E := (cell12965 ⟨56, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20538853993031 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (555060394461 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_57 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82121863213481 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444049126293 / 20000000000000 : ℝ))
      (E := (cell12965 ⟨57, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82121863213481 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444049126293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_58 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (10261041688021 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222024959709 / 10000000000000 : ℝ))
      (E := (cell12965 ⟨58, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (10261041688021 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222024959709 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_59 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (82054826816963 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220253647729 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨59, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (82054826816963 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220253647729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12966_40 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16539083024067 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220062391179 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨40, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16539083024067 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220062391179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_41 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (20665372512537 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220066402809 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨41, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (20665372512537 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220066402809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_42 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41313794241731 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277508796529 / 12500000000000 : ℝ))
      (E := (cell12966 ⟨42, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41313794241731 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277508796529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_43 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41296855195391 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220074415863 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨43, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41296855195391 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220074415863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_44 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41279927871383 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (111003920731 / 5000000000000 : ℝ))
      (E := (cell12966 ⟨44, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41279927871383 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (111003920731 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_45 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16505204902043 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222008242569 / 10000000000000 : ℝ))
      (E := (cell12966 ⟨45, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16505204902043 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (222008242569 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_46 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82492216664079 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110043223611 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨46, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82492216664079 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110043223611 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_47 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82458432175453 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110045209109 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨47, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82458432175453 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110045209109 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_48 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41212335507789 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220094454247 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨48, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41212335507789 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220094454247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_49 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82390933155837 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110049217463 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨49, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82390933155837 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1110049217463 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_50 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41178609283879 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220102475493 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨50, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41178609283879 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220102475493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_51 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82323527223011 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220106455047 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨51, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82323527223011 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220106455047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_52 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41144929546703 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (4440220977 / 200000000000 : ℝ))
      (E := (cell12966 ⟨52, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41144929546703 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (4440220977 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_53 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (5141013384431 / 6250000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220114513513 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨53, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (5141013384431 / 6250000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220114513513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_54 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (20555648091893 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220118526543 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨54, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (20555648091893 / 25000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220118526543 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_55 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41094496857833 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (6937882887 / 312500000000 : ℝ))
      (E := (cell12966 ⟨55, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41094496857833 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (6937882887 / 312500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_56 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41077709083773 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220126501447 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨56, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41077709083773 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220126501447 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_57 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (2053046642393 / 2500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220130514369 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨57, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (2053046642393 / 2500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2220130514369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_58 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (8208833627283 / 10000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (555033639577 / 25000000000000 : ℝ))
      (E := (cell12966 ⟨58, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (8208833627283 / 10000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (555033639577 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_59 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (82054829871657 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (111006928477 / 5000000000000 : ℝ))
      (E := (cell12966 ⟨59, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (82054829871657 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (111006928477 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12967_40 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16539082534713 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (17343338157 / 781250000000 : ℝ))
      (E := (cell12967 ⟨40, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16539082534713 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (17343338157 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_41 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82661487896533 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (277493912939 / 12500000000000 : ℝ))
      (E := (cell12967 ⟨41, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82661487896533 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (277493912939 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_42 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41313793311299 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (110997767011 / 5000000000000 : ℝ))
      (E := (cell12967 ⟨42, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41313793311299 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (110997767011 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_43 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82593708822267 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (69373729193 / 3125000000000 : ℝ))
      (E := (cell12967 ⟨43, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82593708822267 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (69373729193 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_44 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82559854466197 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554990835689 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨44, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82559854466197 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554990835689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_45 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82526023525191 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109983682163 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨45, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82526023525191 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109983682163 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_46 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82492215970199 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219971338123 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨46, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82492215970199 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219971338123 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_47 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41229215886159 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554993844971 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨47, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41229215886159 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554993844971 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_48 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82424670902787 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554994842371 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨48, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82424670902787 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554994842371 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_49 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82390933332993 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (88799336893 / 4000000000000 : ℝ))
      (E := (cell12967 ⟨49, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82390933332993 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (88799336893 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_50 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (82357219034463 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109993708881 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨50, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (82357219034463 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109993708881 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_51 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41161763989433 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554997852961 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨51, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41161763989433 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554997852961 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_52 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (2571558129313 / 3125000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554998850361 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨52, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (2571558129313 / 3125000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554998850361 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_53 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16451243096773 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109999721153 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨53, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16451243096773 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109999721153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_54 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16444518797701 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (555000853189 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨54, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16444518797701 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (555000853189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_55 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (10273624453021 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220007427221 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨55, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (10273624453021 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220007427221 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_56 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (10269427545403 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220011481813 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨56, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (10269427545403 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220011481813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_57 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (4106093408909 / 5000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (444003090819 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨57, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (4106093408909 / 5000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (444003090819 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_58 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (1026104238021 / 1250000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220019458017 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨58, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (1026104238021 / 1250000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2220019458017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_59 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16410966585301 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (222002348907 / 10000000000000 : ℝ))
      (E := (cell12967 ⟨59, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16410966585301 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (222002348907 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12968_40 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41347705113801 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221983229161 / 10000000000000 : ℝ))
      (E := (cell12968 ⟨40, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41347705113801 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221983229161 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_41 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (8266148574369 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219836260099 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨41, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (8266148574369 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219836260099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_42 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10328448095309 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219840305331 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨42, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10328448095309 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219840305331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_43 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41296853627227 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219844308491 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨43, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41296853627227 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219844308491 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_44 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10319981648787 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219848326953 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨44, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10319981648787 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219848326953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_45 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (6447345511 / 7812500000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219852300193 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨45, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (6447345511 / 7812500000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219852300193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_46 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41246107638459 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443971268823 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨46, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41246107638459 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443971268823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_47 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41229215684873 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554965084713 / 25000000000000 : ℝ))
      (E := (cell12968 ⟨47, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41229215684873 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554965084713 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_48 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41212335395263 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443972868203 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨48, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41212335395263 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443972868203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_49 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (20597733377661 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219868348111 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨49, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (20597733377661 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219868348111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_50 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (20589304875407 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109936178719 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨50, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (20589304875407 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109936178719 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_51 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (20580882183787 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219876366083 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨51, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (20580882183787 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219876366083 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_52 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82289861183019 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219880370917 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨52, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82289861183019 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219880370917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_53 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10282027102149 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219884427687 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨53, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10282027102149 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219884427687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_54 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41111297804881 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554972103679 / 25000000000000 : ℝ))
      (E := (cell12968 ⟨54, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41111297804881 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554972103679 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_55 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (513681234581 / 625000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219892446431 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨55, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (513681234581 / 625000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219892446431 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_56 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (82155422559157 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277487050081 / 12500000000000 : ℝ))
      (E := (cell12968 ⟨56, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (82155422559157 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277487050081 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_57 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41060935330431 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219900450643 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨57, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41060935330431 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219900450643 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_58 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41044170905359 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (11099522369 / 500000000000 : ℝ))
      (E := (cell12968 ⟨58, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41044170905359 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (11099522369 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_59 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (20513708995377 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109954232769 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨59, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (20513708995377 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109954232769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12969_40 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16539081556489 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219717296177 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨40, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16539081556489 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219717296177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_41 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82661483591619 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219721272569 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨41, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82661483591619 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219721272569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_42 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41313791451541 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219725267567 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨42, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41313791451541 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219725267567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_43 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (5162106605459 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109864639983 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨43, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (5162106605459 / 6250000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109864639983 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_44 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41279925957531 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109866654173 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨44, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41279925957531 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109866654173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_45 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41263010778521 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110986864609 / 5000000000000 : ℝ))
      (E := (cell12969 ⟨45, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41263010778521 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (110986864609 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_46 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16498442916847 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219741347373 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨46, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16498442916847 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219741347373 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_47 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82458430967739 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219745354057 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨47, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82458430967739 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219745354057 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_48 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16484934135759 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109874684421 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨48, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16484934135759 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109874684421 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_49 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (8239093368879 / 10000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (554938332563 / 25000000000000 : ℝ))
      (E := (cell12969 ⟨49, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (8239093368879 / 10000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (554938332563 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_50 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82357219969253 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277469669191 / 12500000000000 : ℝ))
      (E := (cell12969 ⟨50, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82357219969253 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277469669191 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_51 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82323529491857 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219761376793 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨51, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82323529491857 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219761376793 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_52 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41144931114207 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219765396921 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨52, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41144931114207 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219765396921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_53 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41128109075439 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219769410579 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨53, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41128109075439 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219769410579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_54 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82222597231343 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109886707111 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨54, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82222597231343 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109886707111 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_55 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41094499721021 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109888702049 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨55, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41094499721021 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109888702049 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_56 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (82155424755347 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219781435393 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨56, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (82155424755347 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219781435393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_57 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41060936571883 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219785444843 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨57, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41060936571883 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219785444843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_58 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (10261043072493 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109894714037 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨58, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (10261043072493 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109894714037 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_59 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (10256854879583 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219793439727 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨59, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (10256854879583 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219793439727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12970_40 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41347702669047 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109801148899 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨40, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41347702669047 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109801148899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_41 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41330740720159 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554901570533 / 25000000000000 : ℝ))
      (E := (cell12970 ⟨41, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41330740720159 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554901570533 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_42 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (20656895261107 / 25000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219610285749 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨42, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (20656895261107 / 25000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219610285749 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_43 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16518740824187 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443922861489 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨43, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16518740824187 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443922861489 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_44 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (5159990665031 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219618345801 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨44, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (5159990665031 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219618345801 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_45 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82526020573917 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (34681599067 / 1562500000000 : ℝ))
      (E := (cell12970 ⟨45, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82526020573917 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (34681599067 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_46 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (1649844277843 / 2000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219626347899 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨46, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (1649844277843 / 2000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219626347899 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_47 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16491686113259 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443926073313 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨47, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16491686113259 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443926073313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_48 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (10303083820949 / 12500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219634335049 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨48, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (10303083820949 / 12500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219634335049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_49 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82390933867431 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219638368751 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨49, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82390933867431 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219638368751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_50 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (4117861021867 / 5000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (88785693881 / 4000000000000 : ℝ))
      (E := (cell12970 ⟨50, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (4117861021867 / 5000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (88785693881 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_51 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (2572610320281 / 3125000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109823192473 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨51, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (2572610320281 / 3125000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109823192473 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_52 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (411449316371 / 500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443930084081 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨52, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (411449316371 / 500000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443930084081 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_53 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82256219484921 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109827195493 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨53, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82256219484921 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109827195493 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_54 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82222598853247 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109829205639 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨54, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82222598853247 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109829205639 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_55 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41094500675707 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277457802309 / 12500000000000 : ℝ))
      (E := (cell12970 ⟨55, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41094500675707 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277457802309 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_56 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (5134714184487 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221966640861 / 10000000000000 : ℝ))
      (E := (cell12970 ⟨56, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (5134714184487 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221966640861 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_57 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (82121875626891 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443934087339 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨57, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (82121875626891 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443934087339 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_58 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41044173674679 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221967443923 / 10000000000000 : ℝ))
      (E := (cell12970 ⟨58, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41044173674679 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221967443923 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_59 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41027421045987 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277459808857 / 12500000000000 : ℝ))
      (E := (cell12970 ⟨59, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41027421045987 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (277459808857 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12971_40 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82695402894549 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219487355247 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨40, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82695402894549 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219487355247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_41 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82661479289789 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219491347579 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨41, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82661479289789 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219491347579 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_42 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82627579186511 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (17755962879 / 800000000000 : ℝ))
      (E := (cell12971 ⟨42, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82627579186511 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (17755962879 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_43 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82593702555227 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109749666043 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨43, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82593702555227 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109749666043 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_44 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (20639962341649 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219503380453 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨44, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (20639962341649 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219503380453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_45 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (322367264029 / 390625000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219507385629 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨45, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (322367264029 / 390625000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219507385629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_46 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82492213200663 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443902280921 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨46, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82492213200663 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443902280921 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_47 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41229215082707 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277439422047 / 12500000000000 : ℝ))
      (E := (cell12971 ⟨47, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41229215082707 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277439422047 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_48 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82424670456919 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (34679990883 / 1562500000000 : ℝ))
      (E := (cell12971 ⟨48, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82424670456919 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (34679990883 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_49 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41195467023283 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109761702311 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨49, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41195467023283 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109761702311 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_50 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41178610452943 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109763698469 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨50, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41178610452943 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109763698469 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_51 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (10290441375819 / 12500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (88781257983 / 4000000000000 : ℝ))
      (E := (cell12971 ⟨51, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (10290441375819 / 12500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (88781257983 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_52 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82289864320379 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443907088273 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨52, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82289864320379 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443907088273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_53 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41128110409661 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109769713991 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨53, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41128110409661 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109769713991 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_54 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (20555650118869 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219543464981 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨54, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (20555650118869 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219543464981 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_55 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (3287560130443 / 4000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109773744777 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨55, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (3287560130443 / 4000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109773744777 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_56 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82155429148493 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219551497739 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨56, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82155429148493 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219551497739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_57 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82121878110239 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (221955548537 / 10000000000000 : ℝ))
      (E := (cell12971 ⟨57, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82121878110239 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (221955548537 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_58 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (1026104376487 / 1250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219559507267 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨58, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (1026104376487 / 1250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219559507267 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_59 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (82054845147439 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443912699941 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨59, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (82054845147439 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443912699941 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12972_40 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82695389134537 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109686191947 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨40, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82695389134537 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109686191947 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_41 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16532293109573 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554844104861 / 25000000000000 : ℝ))
      (E := (cell12972 ⟨41, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16532293109573 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554844104861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_42 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (41313782731327 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219380416249 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨42, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (41313782731327 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219380416249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_43 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16518737769883 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109692215937 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨43, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16518737769883 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109692215937 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_44 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82559835678807 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (138711775377 / 6250000000000 : ℝ))
      (E := (cell12972 ⟨44, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82559835678807 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (138711775377 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_45 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (20631501480409 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443878490959 / 20000000000000 : ℝ))
      (E := (cell12972 ⟨45, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (20631501480409 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443878490959 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_46 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82492199548857 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277424557319 / 12500000000000 : ℝ))
      (E := (cell12972 ⟨46, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82492199548857 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277424557319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_47 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (41229208265783 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443880094821 / 20000000000000 : ℝ))
      (E := (cell12972 ⟨47, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (41229208265783 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (443880094821 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_48 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82424656841009 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221940444021 / 10000000000000 : ℝ))
      (E := (cell12972 ⟨48, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82424656841009 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221940444021 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_49 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82390920448573 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219408472273 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨49, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82390920448573 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219408472273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_50 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (20589301831447 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219412508651 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨50, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (20589301831447 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219412508651 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_51 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (10290439680541 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219416487397 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨51, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (10290439680541 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219416487397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_52 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (10286231347001 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109710261711 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨52, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (10286231347001 / 12500000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109710261711 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_53 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (41128103646391 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277428061913 / 12500000000000 : ℝ))
      (E := (cell12972 ⟨53, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (41128103646391 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (277428061913 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_54 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82222586966747 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219428517629 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨54, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82222586966747 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219428517629 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_55 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82188989770137 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221943252759 / 10000000000000 : ℝ))
      (E := (cell12972 ⟨55, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82188989770137 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221943252759 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_56 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82155415675323 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109718260613 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨56, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82155415675323 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109718260613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_57 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (82121864654817 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219440553541 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨57, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (82121864654817 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219440553541 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_58 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16417667336253 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219444561037 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨58, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16417667336253 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219444561037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_59 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (1641096634549 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109724299177 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨59, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (1641096634549 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109724299177 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12973_40 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41347687444059 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219257485363 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨40, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41347687444059 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219257485363 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_41 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16532290261533 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219261517041 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨41, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16532290261533 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219261517041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_42 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (20656887807167 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219265510019 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨42, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (20656887807167 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219265510019 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_43 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82593674621637 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (277408690233 / 12500000000000 : ℝ))
      (E := (cell12973 ⟨43, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82593674621637 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (277408690233 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_44 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82559821457233 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219273492287 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨44, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82559821457233 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219273492287 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_45 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82525991706261 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109638768681 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨45, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82525991706261 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109638768681 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_46 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41246092669837 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109640768739 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨46, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41246092669837 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109640768739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_47 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (20614600582143 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443857109887 / 20000000000000 : ℝ))
      (E := (cell12973 ⟨47, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (20614600582143 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443857109887 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_48 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82424642644199 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (44385791419 / 2000000000000 : ℝ))
      (E := (cell12973 ⟨48, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82424642644199 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (44385791419 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_49 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82390906257941 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219293540549 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨49, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82390906257941 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219293540549 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_50 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (8235719314133 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219297573469 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨50, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (8235719314133 / 10000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219297573469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_51 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41161751633019 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109650803917 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨51, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41161751633019 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109650803917 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_52 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41144918301941 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219305581461 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨52, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41144918301941 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219305581461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_53 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16451238625363 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (22193096091 / 1000000000000 : ℝ))
      (E := (cell12973 ⟨53, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16451238625363 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (22193096091 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_54 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82222572806933 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (88772545127 / 4000000000000 : ℝ))
      (E := (cell12973 ⟨54, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82222572806933 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (88772545127 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_55 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (10273621952059 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221931763493 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨55, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (10273621952059 / 12500000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221931763493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_56 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41077700763901 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (34676900397 / 1562500000000 : ℝ))
      (E := (cell12973 ⟨56, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41077700763901 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (34676900397 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_57 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16424370102687 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219325654609 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨57, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16424370102687 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219325654609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_58 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41044161273009 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219329659037 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨58, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41044161273009 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219329659037 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_59 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (82054817598333 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219333693331 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨59, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (82054817598333 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219333693331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12974_40 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨40, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (41347680321949 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219142582459 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨40, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨40, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (41347680321949 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219142582459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_41 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨41, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82661437069663 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443829322053 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨41, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨41, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82661437069663 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443829322053 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_42 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨42, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (41313768498439 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109575299709 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨42, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨42, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (41313768498439 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109575299709 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_43 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨43, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16518732079211 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554788651871 / 25000000000000 : ℝ))
      (E := (cell12974 ⟨43, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨43, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16518732079211 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554788651871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_44 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨44, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82559807237853 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219158633041 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨44, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨44, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82559807237853 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219158633041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_45 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨45, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82525977493079 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219162615561 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨45, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨45, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82525977493079 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219162615561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_46 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨46, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16498434226537 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (44383333419 / 2000000000000 : ℝ))
      (E := (cell12974 ⟨46, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨46, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16498434226537 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (44383333419 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_47 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨47, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82458388127771 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109585339667 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨47, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨47, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82458388127771 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109585339667 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_48 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨48, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82424628449579 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443834927673 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨48, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨48, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82424628449579 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443834927673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_49 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨49, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82390892069499 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219178663443 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨49, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨49, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82390892069499 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219178663443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_50 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨50, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (4117858947953 / 5000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221918269293 / 10000000000000 : ℝ))
      (E := (cell12974 ⟨50, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨50, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (4117858947953 / 5000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221918269293 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_51 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨51, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82323489089937 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109593361953 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨51, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨51, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82323489089937 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109593361953 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_52 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨52, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82289822433943 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219190694191 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨52, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨52, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82289822433943 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219190694191 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_53 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨53, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (41128089481517 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443838943707 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨53, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨53, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (41128089481517 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443838943707 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_54 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨54, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16444511729861 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219198734359 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨54, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨54, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16444511729861 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219198734359 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_55 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨55, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (82188961464991 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219202737911 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨55, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨55, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (82188961464991 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219202737911 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_56 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨56, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16431077476493 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219206725229 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨56, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨56, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16431077476493 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219206725229 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_57 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨57, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20530459093559 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219210751319 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨57, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨57, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20530459093559 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219210751319 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_58 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨58, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (10261038551619 / 12500000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (55480368817 / 2500000000000 : ℝ))
      (E := (cell12974 ⟨58, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨58, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (10261038551619 / 12500000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (55480368817 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_59 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨59, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20513700867849 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219218783953 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨59, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨59, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20513700867849 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219218783953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

end BstLean.Part268
