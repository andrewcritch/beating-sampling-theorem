import BstLean.Part268CellShard24Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12950_0 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (42036140604681 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444349272089 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨0, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (42036140604681 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444349272089 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_1 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (42018692515521 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555437594343 / 25000000000000 : ℝ))
      (E := (cell12950 ⟨1, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (42018692515521 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (555437594343 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_2 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (42001256837817 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221754374071 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨2, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (42001256837817 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221754374071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_3 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (262398959709 / 312500000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444351683369 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨3, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (262398959709 / 312500000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444351683369 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_4 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20983211322179 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110881199023 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨4, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20983211322179 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110881199023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_5 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41949024092633 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221766383441 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨5, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41949024092633 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221766383441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_6 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83863275760843 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277721304829 / 12500000000000 : ℝ))
      (E := (cell12950 ⟨6, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83863275760843 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277721304829 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_7 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (10478565997493 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110887198537 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨7, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (10478565997493 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110887198537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_8 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (10474225600907 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221778439813 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨8, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (10474225600907 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221778439813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_9 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83759106207647 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110891199829 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨9, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83759106207647 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110891199829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_10 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (8372443214617 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221786399227 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨10, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (8372443214617 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221786399227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_11 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83689782588061 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444358088979 / 20000000000000 : ℝ))
      (E := (cell12950 ⟨11, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83689782588061 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (444358088979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_12 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (41827578749367 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221794426557 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨12, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (41827578749367 / 50000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221794426557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_13 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (16724111368757 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277724808279 / 12500000000000 : ℝ))
      (E := (cell12950 ⟨13, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (16724111368757 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (277724808279 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_14 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83585980588989 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110901226613 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨14, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83585980588989 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110901226613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_15 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (10443928587537 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110903225489 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨15, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (10443928587537 / 12500000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110903225489 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_16 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (20879225285959 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110905232281 / 50000000000000 : ℝ))
      (E := (cell12950 ⟨16, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (20879225285959 / 25000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (1110905232281 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_17 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (8348239788591 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221814440581 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨17, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (8348239788591 / 10000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221814440581 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_18 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (16689583778599 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221818441813 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨18, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (16689583778599 / 20000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221818441813 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12950_19 : CellCertificate 12950 (879835806461043 / 10000000000000000 : ℝ) (405488327832853 / 250000000000000000 : ℝ) (327476364472011 / 10000000000000000 : ℝ)
    (cell12950 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · norm_num [cell12950]
  · have h := gap_lower (n := 12950) (a := (83413464131743 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221822472611 / 100000000000000 : ℝ))
      (E := (cell12950 ⟨19, by decide⟩).energy) (xi := (327476364472011 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12950 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12950]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12950])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12950) (a := (83413464131743 / 100000000000000 : ℝ)) (b := (79510612739 / 50000000000000 : ℝ)) (q := (2221822472611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12950])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12950]

theorem cert12951_0 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (84072266660449 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221630942443 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨0, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (84072266660449 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221630942443 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_1 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (84037370792683 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110817469237 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨1, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (84037370792683 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110817469237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_2 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (84002499747389 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110819486437 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨2, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (84002499747389 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110819486437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_3 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83967653488313 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221642938297 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨3, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83967653488313 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221642938297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_4 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (8393283197939 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555411739667 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨4, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (8393283197939 / 10000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555411739667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_5 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41949017592373 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222165098399 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨5, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41949017592373 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222165098399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_6 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83863263068693 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444330992783 / 20000000000000 : ℝ))
      (E := (cell12951 ⟨6, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83863263068693 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (444330992783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_7 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (20957128898933 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555414740937 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨7, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (20957128898933 / 25000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555414740937 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_8 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83793792730549 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221662990611 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨8, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83793792730549 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221662990611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_9 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83759094438013 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555416748333 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨9, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83759094438013 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555416748333 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_10 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83724420683179 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221670978461 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨10, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83724420683179 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221670978461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_11 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41844885715641 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110837505197 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨11, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41844885715641 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110837505197 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_12 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83655146647739 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (88867159161 / 4000000000000 : ℝ))
      (E := (cell12951 ⟨12, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83655146647739 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (88867159161 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_13 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41810273149073 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222168300637 / 10000000000000 : ℝ))
      (E := (cell12951 ⟨13, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41810273149073 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (222168300637 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_14 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83585970348279 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221686981739 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨14, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83585970348279 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221686981739 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_15 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83551418764089 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (8886764107 / 400000000000 : ℝ))
      (E := (cell12951 ⟨15, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83551418764089 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (8886764107 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_16 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (16703378302341 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110847515067 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨16, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (16703378302341 / 20000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110847515067 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_17 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (83482388557431 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555424749163 / 25000000000000 : ℝ))
      (E := (cell12951 ⟨17, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (83482388557431 / 100000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (555424749163 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_18 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (41723954933873 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221702989081 / 100000000000000 : ℝ))
      (E := (cell12951 ⟨18, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (41723954933873 / 50000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (2221702989081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12951_19 : CellCertificate 12951 (879808897207917 / 10000000000000000 : ℝ) (40545700831579 / 25000000000000000 : ℝ) (81862621453933 / 2500000000000000 : ℝ)
    (cell12951 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · norm_num [cell12951]
  · have h := gap_lower (n := 12951) (a := (834134554093 / 1000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110853505887 / 50000000000000 : ℝ))
      (E := (cell12951 ⟨19, by decide⟩).energy) (xi := (81862621453933 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12951 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12951]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12951])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12951) (a := (834134554093 / 1000000000000 : ℝ)) (b := (3180176057 / 2000000000000 : ℝ)) (q := (1110853505887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12951])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12951]

theorem cert12952_0 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (42036126056893 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110757760003 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨0, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (42036126056893 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110757760003 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_1 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (16807471311307 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110759747591 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨1, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (16807471311307 / 20000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110759747591 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_2 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (2100062145533 / 2500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221523509437 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨2, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (2100062145533 / 2500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221523509437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_3 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20991909967971 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221527513333 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨3, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20991909967971 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221527513333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_4 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41966409336083 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221531515007 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨4, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41966409336083 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221531515007 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_5 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (8389802218629 / 10000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221535522343 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨5, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (8389802218629 / 10000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221535522343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_6 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (20965812594643 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110769771483 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨6, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (20965812594643 / 25000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110769771483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_7 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (10478562901689 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221543526253 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨7, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (10478562901689 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221543526253 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_8 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83793780655797 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221547537277 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨8, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83793780655797 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221547537277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_9 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (41879541335149 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110775762433 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨9, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (41879541335149 / 50000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110775762433 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_10 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (8372440922207 / 10000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221555553637 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨10, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (8372440922207 / 10000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221555553637 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_11 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83689760276349 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (69423736621 / 3125000000000 : ℝ))
      (E := (cell12952 ⟨11, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83689760276349 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (69423736621 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_12 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83655135798553 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (3554501737 / 160000000000 : ℝ))
      (E := (cell12952 ⟨12, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83655135798553 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (3554501737 / 160000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_13 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (2090513393857 / 2500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221567542563 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨13, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (2090513393857 / 2500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221567542563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_14 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (10448245013663 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110785782253 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨14, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (10448245013663 / 12500000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110785782253 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_15 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (4177570441479 / 5000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110787799327 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨15, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (4177570441479 / 5000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110787799327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_16 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83516881881237 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221579591873 / 100000000000000 : ℝ))
      (E := (cell12952 ⟨16, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83516881881237 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (2221579591873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_17 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (4174118961529 / 5000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110791803579 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨17, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (4174118961529 / 5000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110791803579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_18 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83447900844087 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444317518169 / 20000000000000 : ℝ))
      (E := (cell12952 ⟨18, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83447900844087 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (444317518169 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12952_19 : CellCertificate 12952 (439890995968397 / 5000000000000000 : ℝ) (40542569363653 / 25000000000000000 : ℝ) (5116009551369 / 156250000000000 : ℝ)
    (cell12952 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · norm_num [cell12952]
  · have h := gap_lower (n := 12952) (a := (83413446688411 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110795802747 / 50000000000000 : ℝ))
      (E := (cell12952 ⟨19, by decide⟩).energy) (xi := (5116009551369 / 156250000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12952 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12952]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12952])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12952) (a := (83413446688411 / 100000000000000 : ℝ)) (b := (39749095543 / 25000000000000 : ℝ)) (q := (1110795802747 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12952])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12952]

theorem cert12953_0 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (84072237569371 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221400093137 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨0, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (84072237569371 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221400093137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_1 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (420186711613 / 500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277675513169 / 12500000000000 : ℝ))
      (E := (cell12953 ⟨1, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (420186711613 / 500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (277675513169 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_2 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (3360098875897 / 4000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110704049763 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨2, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (3360098875897 / 4000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110704049763 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_3 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83967626257593 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221412141957 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨3, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83967626257593 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221412141957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_4 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41966402683521 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444283224999 / 20000000000000 : ℝ))
      (E := (cell12953 ⟨4, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41966402683521 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444283224999 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_5 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83898009189899 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555355028601 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨5, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83898009189899 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555355028601 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_6 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41931618845239 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221424117811 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨6, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41931618845239 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221424117811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_7 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41914245416641 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555357035647 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨7, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41914245416641 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555357035647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_8 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83793768582999 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444286427567 / 20000000000000 : ℝ))
      (E := (cell12953 ⟨8, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83793768582999 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444286427567 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_9 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (167518141809 / 200000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110718084199 / 50000000000000 : ℝ))
      (E := (cell12953 ⟨9, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (167518141809 / 200000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (1110718084199 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_10 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83724397762841 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221440124759 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨10, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83724397762841 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221440124759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_11 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (4184487456163 / 5000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221444129333 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨11, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (4184487456163 / 5000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221444129333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_12 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (10456890618897 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221448188243 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨12, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (10456890618897 / 12500000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221448188243 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_13 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16724105042437 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221452191091 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨13, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16724105042437 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221452191091 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_14 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (41792974936033 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444291228673 / 20000000000000 : ℝ))
      (E := (cell12953 ⟨14, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (41792974936033 / 50000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (444291228673 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_15 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83551398896771 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221460166687 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨15, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83551398896771 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221460166687 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_16 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83516872252433 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555366051997 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨16, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83516872252433 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555366051997 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_17 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (16696473981071 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222146821387 / 10000000000000 : ℝ))
      (E := (cell12953 ⟨17, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (16696473981071 / 20000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (222146821387 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_18 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83447891822019 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555368047213 / 25000000000000 : ℝ))
      (E := (cell12953 ⟨18, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83447891822019 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (555368047213 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12953_19 : CellCertificate 12953 (439877545323373 / 5000000000000000 : ℝ) (12668574493561 / 7812500000000000 : ℝ) (20462421305413 / 625000000000000 : ℝ)
    (cell12953 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · norm_num [cell12953]
  · have h := gap_lower (n := 12953) (a := (83413437969077 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221476195493 / 100000000000000 : ℝ))
      (E := (cell12953 ⟨19, by decide⟩).energy) (xi := (20462421305413 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12953 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12953]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12953])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12953) (a := (83413437969077 / 100000000000000 : ℝ)) (b := (158983963443 / 100000000000000 : ℝ)) (q := (2221476195493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12953])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12953]

theorem cert12954_0 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (16814444605441 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221284719671 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨0, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (16814444605441 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221284719671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_1 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (21009332022719 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221288768987 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨1, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (21009332022719 / 25000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221288768987 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_2 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (16800491595141 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221292743139 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨2, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (16800491595141 / 20000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221292743139 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_3 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (262398789517 / 312500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221296766261 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨3, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (262398789517 / 312500000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221296766261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_4 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83932792064019 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221300730701 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨4, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83932792064019 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221300730701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_5 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83897996195571 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110652380087 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨5, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83897996195571 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110652380087 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_6 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83863225004411 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (88852349857 / 4000000000000 : ℝ))
      (E := (cell12954 ⟨6, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83863225004411 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (88852349857 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_7 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83828478455043 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444262550951 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨7, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83828478455043 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444262550951 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_8 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41896878256077 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444263358457 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨8, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41896878256077 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444263358457 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_9 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83759059140619 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (69416273431 / 3125000000000 : ℝ))
      (E := (cell12954 ⟨9, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83759059140619 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (69416273431 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_10 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41862193152747 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221324749893 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨10, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41862193152747 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221324749893 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_11 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (5230608623251 / 6250000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221328798959 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨11, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (5230608623251 / 6250000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221328798959 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_12 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41827557052803 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110666393441 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨12, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41827557052803 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110666393441 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_13 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41810257335931 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (34708387149 / 1562500000000 : ℝ))
      (E := (cell12954 ⟨13, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41810257335931 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (34708387149 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_14 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41792969818281 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110670388241 / 50000000000000 : ℝ))
      (E := (cell12954 ⟨14, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41792969818281 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (1110670388241 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_15 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83551388965661 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555336197259 / 25000000000000 : ℝ))
      (E := (cell12954 ⟨15, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83551388965661 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (555336197259 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_16 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (83516862625291 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221348820271 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨16, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (83516862625291 / 100000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221348820271 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_17 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41741180290879 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444270563357 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨17, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41741180290879 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444270563357 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_18 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41723941400771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444271368271 / 20000000000000 : ℝ))
      (E := (cell12954 ⟨18, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41723941400771 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (444271368271 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12954_19 : CellCertificate 12954 (879728193336847 / 10000000000000000 : ℝ) (810726157573871 / 500000000000000000 : ℝ) (327372874611657 / 10000000000000000 : ℝ)
    (cell12954 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · norm_num [cell12954]
  · have h := gap_lower (n := 12954) (a := (41706714625649 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221360840049 / 100000000000000 : ℝ))
      (E := (cell12954 ⟨19, by decide⟩).energy) (xi := (327372874611657 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12954 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12954]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12954])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12954) (a := (41706714625649 / 50000000000000 : ℝ)) (b := (19871443333 / 12500000000000 : ℝ)) (q := (2221360840049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12954])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12954]

theorem cert12955_0 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (84072208487287 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277646174951 / 12500000000000 : ℝ))
      (E := (cell12955 ⟨0, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (84072208487287 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277646174951 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_1 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (84037313861363 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222117337037 / 10000000000000 : ℝ))
      (E := (cell12955 ⟨1, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (84037313861363 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222117337037 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_2 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (84002444056159 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221177382397 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨2, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (84002444056159 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221177382397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_3 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (2623987469857 / 3125000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221181386247 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨3, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (2623987469857 / 3125000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221181386247 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_4 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83932778763097 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444237078011 / 20000000000000 : ℝ))
      (E := (cell12955 ⟨4, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83932778763097 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444237078011 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_5 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83897983203307 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221189401701 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨5, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83897983203307 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221189401701 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_6 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83863212320371 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222119342881 / 10000000000000 : ℝ))
      (E := (cell12955 ⟨6, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83863212320371 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (222119342881 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_7 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83828466078793 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110598710377 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨7, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83828466078793 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110598710377 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_8 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (654638628463 / 781250000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555300360651 / 25000000000000 : ℝ))
      (E := (cell12955 ⟨8, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (654638628463 / 781250000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (555300360651 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_9 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16751809475731 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444241088637 / 20000000000000 : ℝ))
      (E := (cell12955 ⟨9, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16751809475731 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (444241088637 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_10 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41862187425013 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110604714521 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨10, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41862187425013 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110604714521 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_11 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16737945364523 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221213406477 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨11, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16737945364523 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221213406477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_12 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83655103261843 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277652179957 / 12500000000000 : ℝ))
      (E := (cell12955 ⟨12, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83655103261843 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (277652179957 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_13 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83620504133309 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221221418177 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨13, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83620504133309 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221221418177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_14 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83585929402793 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110612731927 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨14, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83585929402793 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110612731927 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_15 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83551379036249 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221229465703 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨15, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83551379036249 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221229465703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_16 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (83516852999811 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221233428723 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨16, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (83516852999811 / 100000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221233428723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_17 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (41741175629893 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (111061873707 / 5000000000000 : ℝ))
      (E := (cell12955 ⟨17, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (41741175629893 / 50000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (111061873707 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_18 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (16689574756531 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221241490101 / 100000000000000 : ℝ))
      (E := (cell12955 ⟨18, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (16689574756531 / 20000000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (2221241490101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12955_19 : CellCertificate 12955 (879701300006171 / 10000000000000000 : ℝ) (810663557228721 / 500000000000000000 : ℝ) (81836753115427 / 2500000000000000 : ℝ)
    (cell12955 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · norm_num [cell12955]
  · have h := gap_lower (n := 12955) (a := (2606669391721 / 3125000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110622740443 / 50000000000000 : ℝ))
      (E := (cell12955 ⟨19, by decide⟩).energy) (xi := (81836753115427 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12955 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12955]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12955])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12955) (a := (2606669391721 / 3125000000000 : ℝ)) (b := (79479565917 / 50000000000000 : ℝ)) (q := (1110622740443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12955])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12955]

theorem cert12956_0 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (84072193949617 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444210815023 / 20000000000000 : ℝ))
      (E := (cell12956 ⟨0, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (84072193949617 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (444210815023 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_1 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (84037299634061 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221058083077 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨1, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (84037299634061 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221058083077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_2 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (42001215069393 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (138816379699 / 6250000000000 : ℝ))
      (E := (cell12956 ⟨2, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (42001215069393 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (138816379699 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_3 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (10495948178443 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221066059823 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨3, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (10495948178443 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221066059823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_4 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83932765464273 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110535051531 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨4, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83932765464273 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110535051531 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_5 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (16779594042621 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221074096941 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨5, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (16779594042621 / 20000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221074096941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_6 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83863199638357 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221078106993 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨6, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83863199638357 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221078106993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_7 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41914226852267 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221082082587 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨7, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41914226852267 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221082082587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_8 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (3351749295053 / 4000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221086088797 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨8, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (3351749295053 / 4000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221086088797 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_9 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (5234939726163 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221090074441 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨9, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (5234939726163 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221090074441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_10 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41862181698219 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110547052069 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨10, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41862181698219 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110547052069 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_11 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41844857837529 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221098126163 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨11, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41844857837529 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221098126163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_12 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83655092419887 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555275522113 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨12, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83655092419887 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555275522113 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_13 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (5226280849783 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277638264127 / 12500000000000 : ℝ))
      (E := (cell12956 ⟨13, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (5226280849783 / 6250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (277638264127 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_14 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (41792959585379 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110555044581 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨14, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (41792959585379 / 50000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110555044581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_15 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (10443921138567 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110557069251 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨15, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (10443921138567 / 12500000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110557069251 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_16 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83516843375993 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555279537441 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨16, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83516843375993 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555279537441 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_17 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (1043529274243 / 1250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110561063851 / 50000000000000 : ℝ))
      (E := (cell12956 ⟨17, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (1043529274243 / 1250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (1110561063851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_18 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (83447864765357 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221126135093 / 100000000000000 : ℝ))
      (E := (cell12956 ⟨18, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (83447864765357 / 100000000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (2221126135093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12956_19 : CellCertificate 12956 (27489825332931 / 312500000000000 : ℝ) (1621201933100429 / 1000000000000000000 : ℝ) (327321154435711 / 10000000000000000 : ℝ)
    (cell12956 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · norm_num [cell12956]
  · have h := gap_lower (n := 12956) (a := (208533529551 / 250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555282529501 / 25000000000000 : ℝ))
      (E := (cell12956 ⟨19, by decide⟩).energy) (xi := (327321154435711 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12956 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12956]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12956])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12956) (a := (208533529551 / 250000000000 : ℝ)) (b := (19868339869 / 12500000000000 : ℝ)) (q := (555282529501 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12956])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12956]

theorem cert12957_0 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (84072179414193 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110469373097 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨0, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (84072179414193 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110469373097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_1 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (10504660676121 / 12500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69404460423 / 3125000000000 : ℝ))
      (E := (cell12957 ⟨1, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (10504660676121 / 12500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (69404460423 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_2 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (42001208111793 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220946763617 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨2, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (42001208111793 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220946763617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_3 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (419837859109 / 500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220950786989 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨3, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (419837859109 / 500000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220950786989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_4 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (1678655043351 / 2000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (111047737693 / 5000000000000 : ℝ))
      (E := (cell12957 ⟨4, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (1678655043351 / 2000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (111047737693 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_5 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41948978612483 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220958787941 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨5, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41948978612483 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220958787941 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_6 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83863186958369 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (555240695243 / 25000000000000 : ℝ))
      (E := (cell12957 ⟨6, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83863186958369 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (555240695243 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_7 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83828441332263 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444193359651 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨7, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83828441332263 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444193359651 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_8 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (4189686015567 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220970788883 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨8, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (4189686015567 / 5000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220970788883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_9 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20939755965119 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220974817699 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨9, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20939755965119 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220974817699 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_10 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (8372435194473 / 10000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220978775181 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨10, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (8372435194473 / 10000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220978775181 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_11 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83689704529343 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110491391871 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨11, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83689704529343 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110491391871 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_12 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41827540789869 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110493395693 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨12, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41827540789869 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110493395693 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_13 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (20905120765379 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444198160783 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨13, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (20905120765379 / 25000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444198160783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_14 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83585908940457 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (222099482689 / 10000000000000 : ℝ))
      (E := (cell12957 ⟨14, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83585908940457 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (222099482689 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_15 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83551359182519 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220998807437 / 100000000000000 : ℝ))
      (E := (cell12957 ⟨15, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83551359182519 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (2220998807437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_16 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83516833753837 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110501404383 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨16, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83516833753837 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110501404383 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_17 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (83482332620719 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444201367141 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨17, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (83482332620719 / 100000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444201367141 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_18 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (5215490984353 / 6250000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444202166917 / 20000000000000 : ℝ))
      (E := (cell12957 ⟨18, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (5215490984353 / 6250000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (444202166917 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12957_19 : CellCertificate 12957 (13744492582481 / 156250000000000 : ℝ) (64843070842889 / 40000000000000000 : ℝ) (81823825133153 / 2500000000000000 : ℝ)
    (cell12957 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · norm_num [cell12957]
  · have h := gap_lower (n := 12957) (a := (41706701553641 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110507433981 / 50000000000000 : ℝ))
      (E := (cell12957 ⟨19, by decide⟩).energy) (xi := (81823825133153 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12957 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12957]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12957])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12957) (a := (41706701553641 / 50000000000000 : ℝ)) (b := (79467154009 / 50000000000000 : ℝ)) (q := (1110507433981 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12957])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12957]

theorem cert12958_0 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16814432976203 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110411735341 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨0, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16814432976203 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110411735341 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_1 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (21009317796521 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220827495323 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨1, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (21009317796521 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220827495323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_2 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (84002402310559 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (111041575279 / 5000000000000 : ℝ))
      (E := (cell12958 ⟨2, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (84002402310559 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (111041575279 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_3 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (5247972388637 / 6250000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110417754921 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨3, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (5247972388637 / 6250000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110417754921 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_4 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (20983184718231 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220839516241 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨4, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (20983184718231 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220839516241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_5 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83897944238889 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110421737351 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨5, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83897944238889 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110421737351 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_6 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16772634856081 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220847508729 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨6, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16772634856081 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220847508729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_7 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (4191421448099 / 5000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220851509761 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨7, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (4191421448099 / 5000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220851509761 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_8 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41896854124153 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444171096969 / 20000000000000 : ℝ))
      (E := (cell12958 ⟨8, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41896854124153 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444171096969 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_9 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83759012104259 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277607437353 / 12500000000000 : ℝ))
      (E := (cell12958 ⟨9, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83759012104259 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (277607437353 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_10 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (837243404949 / 1000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555215875061 / 25000000000000 : ℝ))
      (E := (cell12958 ⟨10, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (837243404949 / 1000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555215875061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_11 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83689693385471 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220867553493 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨11, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83689693385471 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220867553493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_12 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (16731014148279 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220871548459 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨12, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (16731014148279 / 20000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220871548459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_13 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (41810236264137 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444175109803 / 20000000000000 : ℝ))
      (E := (cell12958 ⟨13, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (41810236264137 / 50000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (444175109803 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_14 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83585898711889 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110439780359 / 50000000000000 : ℝ))
      (E := (cell12958 ⟨14, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83585898711889 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (1110439780359 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_15 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (417756746291 / 500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220883530693 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨15, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (417756746291 / 500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220883530693 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_16 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83516824133341 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (44417750443 / 2000000000000 : ℝ))
      (E := (cell12958 ⟨16, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83516824133341 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (44417750443 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_17 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (83482323303623 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220891539917 / 100000000000000 : ℝ))
      (E := (cell12958 ⟨17, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (83482323303623 / 100000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (2220891539917 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_18 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (10430980841941 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555223882581 / 25000000000000 : ℝ))
      (E := (cell12958 ⟨18, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (10430980841941 / 12500000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (555223882581 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12958_19 : CellCertificate 12958 (879620643880221 / 10000000000000000 : ℝ) (1620951628368353 / 1000000000000000000 : ℝ) (163634725375681 / 5000000000000000 : ℝ)
    (cell12958 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · norm_num [cell12958]
  · have h := gap_lower (n := 12958) (a := (20853348598929 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88835982237 / 4000000000000 : ℝ))
      (E := (cell12958 ⟨19, by decide⟩).energy) (xi := (163634725375681 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12958 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12958]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12958])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12958) (a := (20853348598929 / 25000000000000 : ℝ)) (b := (158921899031 / 100000000000000 : ℝ)) (q := (88835982237 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12958])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12958]

theorem cert12959_0 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (21018037587521 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2168660399 / 97656250000 : ℝ))
      (E := (cell12959 ⟨0, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (21018037587521 / 25000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2168660399 / 97656250000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_1 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (8403725696541 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (27758903159 / 1250000000000 : ℝ))
      (E := (cell12959 ⟨1, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (8403725696541 / 10000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (27758903159 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_2 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (84002388399703 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220716243193 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨2, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (84002388399703 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220716243193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_3 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41983772308359 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220720228381 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨3, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41983772308359 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220720228381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_4 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83932725580397 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220724216417 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨4, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83932725580397 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220724216417 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_5 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83897931254873 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220728273129 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨5, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83897931254873 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220728273129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_6 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83863161604467 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110366116141 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨6, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83863161604467 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110366116141 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_7 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41914208296843 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220736275101 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨7, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41914208296843 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220736275101 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_8 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (10474212023403 / 12500000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220740234703 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨8, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (10474212023403 / 12500000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220740234703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_9 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41879500174979 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138796518247 / 6250000000000 : ℝ))
      (E := (cell12959 ⟨9, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41879500174979 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (138796518247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_10 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83724329046949 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555187069831 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨10, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83724329046949 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555187069831 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_11 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83689682243441 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220752261137 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨11, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83689682243441 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220752261137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_12 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83655059904857 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220756301557 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨12, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83655059904857 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220756301557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_13 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83620461996801 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (88830411607 / 4000000000000 : ℝ))
      (E := (cell12959 ⟨13, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83620461996801 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (88830411607 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_14 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (16717177697011 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110382145321 / 50000000000000 : ℝ))
      (E := (cell12959 ⟨14, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (16717177697011 / 20000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (1110382145321 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_15 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41775669667789 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220768308269 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨15, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41775669667789 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220768308269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_16 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83516814514507 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (444154457983 / 20000000000000 : ℝ))
      (E := (cell12959 ⟨16, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83516814514507 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (444154457983 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_17 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83482313988151 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220776298571 / 100000000000000 : ℝ))
      (E := (cell12959 ⟨17, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83482313988151 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (2220776298571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_18 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (83447837722997 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555195070141 / 25000000000000 : ℝ))
      (E := (cell12959 ⟨18, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (83447837722997 / 100000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (555195070141 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12959_19 : CellCertificate 12959 (43979688322859 / 500000000000000 : ℝ) (1620826504984339 / 1000000000000000000 : ℝ) (81810901272727 / 2500000000000000 : ℝ)
    (cell12959 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · norm_num [cell12959]
  · have h := gap_lower (n := 12959) (a := (41706692842851 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (44415685969 / 2000000000000 : ℝ))
      (E := (cell12959 ⟨19, by decide⟩).energy) (xi := (81810901272727 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12959 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12959]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12959])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12959) (a := (41706692842851 / 50000000000000 : ℝ)) (b := (19863686499 / 12500000000000 : ℝ)) (q := (44415685969 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12959])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12959]

theorem cert12960_0 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (84072135821397 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (69393531939 / 3125000000000 : ℝ))
      (E := (cell12960 ⟨0, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (84072135821397 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (69393531939 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_1 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (84037242746943 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220597005731 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨1, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (84037242746943 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220597005731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_2 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (84002374491019 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110300517169 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨2, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (84002374491019 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110300517169 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_3 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83967531017379 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110302500257 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨3, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83967531017379 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110302500257 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_4 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (5245794518123 / 6250000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220609028177 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨4, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (5245794518123 / 6250000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220609028177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_5 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41948959136459 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220613009369 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨5, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41948959136459 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220613009369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_6 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83863148930553 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110308504807 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨6, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83863148930553 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110308504807 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_7 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83828404227379 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220621036281 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨7, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83828404227379 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220621036281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_8 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20948421032023 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110312519231 / 50000000000000 : ℝ))
      (E := (cell12960 ⟨8, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20948421032023 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (1110312519231 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_9 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83758988597571 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555157255737 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨9, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83758988597571 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555157255737 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_10 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20931079400219 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555158263589 / 25000000000000 : ℝ))
      (E := (cell12960 ⟨10, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20931079400219 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (555158263589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_11 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20922417775813 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (138789813929 / 6250000000000 : ℝ))
      (E := (cell12960 ⟨11, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20922417775813 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (138789813929 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_12 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (669240392561 / 800000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (55516026267 / 2500000000000 : ℝ))
      (E := (cell12960 ⟨12, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (669240392561 / 800000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (55516026267 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_13 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83620451467097 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (11103225137 / 500000000000 : ℝ))
      (E := (cell12960 ⟨13, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83620451467097 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (11103225137 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_14 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83585878259953 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220649074831 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨14, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83585878259953 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220649074831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_15 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20887832353663 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444130616397 / 20000000000000 : ℝ))
      (E := (cell12960 ⟨15, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20887832353663 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (444130616397 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_16 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (20879201224333 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220657053857 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨16, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (20879201224333 / 25000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220657053857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_17 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (163051376317 / 195312500000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220661053437 / 100000000000000 : ℝ))
      (E := (cell12960 ⟨17, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (163051376317 / 195312500000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (2220661053437 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_18 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (41723914356027 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (222066508531 / 10000000000000 : ℝ))
      (E := (cell12960 ⟨18, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (41723914356027 / 50000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (222066508531 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12960_19 : CellCertificate 12960 (439783446504367 / 5000000000000000 : ℝ) (405175350228927 / 250000000000000000 : ℝ) (1636088817751 / 50000000000000 : ℝ)
    (cell12960 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · norm_num [cell12960]
  · have h := gap_lower (n := 12960) (a := (83413376977241 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (111033454777 / 5000000000000 : ℝ))
      (E := (cell12960 ⟨19, by decide⟩).energy) (xi := (1636088817751 / 50000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12960 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12960]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12960])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12960) (a := (83413376977241 / 100000000000000 : ℝ)) (b := (79448543449 / 50000000000000 : ℝ)) (q := (111033454777 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12960])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12960]

theorem cert12961_0 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (21018030323739 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220477791093 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨0, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (21018030323739 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220477791093 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_1 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (16807445706137 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220481812213 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨1, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (16807445706137 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220481812213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_2 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (42001180292253 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110242910567 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨2, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (42001180292253 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110242910567 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_3 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (3358700696807 / 4000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220489826241 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨3, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (3358700696807 / 4000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220489826241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_4 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (20983174750409 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138780864729 / 6250000000000 : ℝ))
      (E := (cell12961 ⟨4, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (20983174750409 / 25000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138780864729 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_5 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (2621809540407 / 3125000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (88819911973 / 4000000000000 : ℝ))
      (E := (cell12961 ⟨5, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (2621809540407 / 3125000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (88819911973 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_6 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41931568129331 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555125460181 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨6, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41931568129331 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555125460181 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_7 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83828391863059 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (22205058513 / 1000000000000 : ℝ))
      (E := (cell12961 ⟨7, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83828391863059 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (22205058513 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_8 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83793672070911 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138781864881 / 6250000000000 : ℝ))
      (E := (cell12961 ⟨8, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83793672070911 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (138781864881 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_9 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83758976847097 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444102761581 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨9, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83758976847097 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444102761581 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_10 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (2093107653917 / 2500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111025891267 / 5000000000000 : ℝ))
      (E := (cell12961 ⟨10, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (2093107653917 / 2500000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (111025891267 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_11 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (16737931992981 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220521838671 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨11, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (16737931992981 / 20000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220521838671 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_12 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83655038237197 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110262926973 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨12, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83655038237197 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110262926973 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_13 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83620440939161 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110264938483 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨13, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83620440939161 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110264938483 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_14 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83585868036583 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (27756673189 / 1250000000000 : ℝ))
      (E := (cell12961 ⟨14, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83585868036583 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (27756673189 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_15 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41775659747711 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220537851837 / 100000000000000 : ℝ))
      (E := (cell12961 ⟨15, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41775659747711 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (2220537851837 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_16 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83516795281817 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110270936091 / 50000000000000 : ℝ))
      (E := (cell12961 ⟨16, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83516795281817 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (1110270936091 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_17 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (521764346013 / 625000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555136465687 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨17, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (521764346013 / 625000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555136465687 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_18 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (41723909851349 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444109977261 / 20000000000000 : ℝ))
      (E := (cell12961 ⟨18, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (41723909851349 / 50000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (444109977261 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12961_19 : CellCertificate 12961 (879540023533959 / 10000000000000000 : ℝ) (1620576316157989 / 1000000000000000000 : ℝ) (327191926128189 / 10000000000000000 : ℝ)
    (cell12961 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · norm_num [cell12961]
  · have h := gap_lower (n := 12961) (a := (83413368270331 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555138472229 / 25000000000000 : ℝ))
      (E := (cell12961 ⟨19, by decide⟩).energy) (xi := (327191926128189 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12961 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12961]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12961])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12961) (a := (83413368270331 / 100000000000000 : ℝ)) (b := (158884683751 / 100000000000000 : ℝ)) (q := (555138472229 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12961])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12961]

theorem cert12962_0 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (42036053385379 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220362613553 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨0, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (42036053385379 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220362613553 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_1 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (84037214316633 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220366614313 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨1, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (84037214316633 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220366614313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_2 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (84002346680163 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (34693290681 / 1562500000000 : ℝ))
      (E := (cell12962 ⟨2, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (84002346680163 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (34693290681 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_3 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83967503825103 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220374647661 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨3, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83967503825103 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220374647661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_4 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (419663428577 / 500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220378638881 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨4, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (419663428577 / 500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220378638881 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_5 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (8389789231519 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220382643 / 100000000000 : ℝ))
      (E := (cell12962 ⟨5, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (8389789231519 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220382643 / 100000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_6 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (16772624717759 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110193333819 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨6, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (16772624717759 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110193333819 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_7 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41914189750363 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220390662161 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨7, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41914189750363 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220390662161 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_8 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83793660015681 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220394633609 / 100000000000000 : ℝ))
      (E := (cell12962 ⟨8, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83793660015681 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (2220394633609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_9 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41879482549269 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (277549830853 / 12500000000000 : ℝ))
      (E := (cell12962 ⟨9, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41879482549269 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (277549830853 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_10 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41862147357181 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110201325173 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨10, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41862147357181 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110201325173 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_11 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41844824414199 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222040665047 / 10000000000000 : ℝ))
      (E := (cell12962 ⟨11, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41844824414199 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (222040665047 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_12 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (83655027406073 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110205326621 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨12, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (83655027406073 / 100000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110205326621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_13 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41810215206497 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110207332229 / 50000000000000 : ℝ))
      (E := (cell12962 ⟨13, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41810215206497 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (1110207332229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_14 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (16717171562989 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (88816747587 / 4000000000000 : ℝ))
      (E := (cell12962 ⟨14, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (16717171562989 / 20000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (88816747587 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_15 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (2610978424309 / 3125000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444084535203 / 20000000000000 : ℝ))
      (E := (cell12962 ⟨15, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (2610978424309 / 3125000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (444084535203 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_16 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (41758392833981 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555106671671 / 25000000000000 : ℝ))
      (E := (cell12962 ⟨16, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (41758392833981 / 50000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (555106671671 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_17 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (2087057151287 / 2500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138776916767 / 6250000000000 : ℝ))
      (E := (cell12962 ⟨17, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (2087057151287 / 2500000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (138776916767 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_18 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (8344781069493 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (44408693671 / 2000000000000 : ℝ))
      (E := (cell12962 ⟨18, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (8344781069493 / 10000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (44408693671 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12962_19 : CellCertificate 12962 (219878289507983 / 2500000000000000 : ℝ) (1620451250706711 / 1000000000000000000 : ℝ) (20447880801489 / 625000000000000 : ℝ)
    (cell12962 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · norm_num [cell12962]
  · have h := gap_lower (n := 12962) (a := (20853339891243 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111021933929 / 5000000000000 : ℝ))
      (E := (cell12962 ⟨19, by decide⟩).energy) (xi := (20447880801489 / 625000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12962 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12962]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12962])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12962) (a := (20853339891243 / 25000000000000 : ℝ)) (b := (39718070637 / 25000000000000 : ℝ)) (q := (111021933929 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12962])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12962]

theorem cert12963_0 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16814418449761 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (138765468089 / 6250000000000 : ℝ))
      (E := (cell12963 ⟨0, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16814418449761 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (138765468089 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_1 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (84037200104789 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555062867471 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨1, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (84037200104789 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555062867471 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_2 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (8400233277799 / 10000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220255439569 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨2, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (8400233277799 / 10000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220255439569 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_3 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16793498046433 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (222025946477 / 10000000000000 : ℝ))
      (E := (cell12963 ⟨3, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16793498046433 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (222025946477 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_4 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83932672431261 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110131747877 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨4, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83932672431261 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110131747877 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_5 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16779575867883 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220267482441 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨5, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16779575867883 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220267482441 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_6 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (1677262218419 / 2000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555067872589 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨6, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (1677262218419 / 2000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555067872589 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_7 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (4191418357019 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220275468861 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨7, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (4191418357019 / 5000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220275468861 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_8 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83793647962399 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (88811179321 / 4000000000000 : ℝ))
      (E := (cell12963 ⟨8, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83793647962399 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (88811179321 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_9 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83758953351891 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220283481659 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨9, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83758953351891 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220283481659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_10 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (261638385231 / 312500000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (69383985293 / 3125000000000 : ℝ))
      (E := (cell12963 ⟨10, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (261638385231 / 312500000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (69383985293 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_11 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (83689637693731 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220291516353 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨11, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (83689637693731 / 100000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220291516353 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_12 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41827508288377 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220295506679 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨12, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41827508288377 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220295506679 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_13 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41810209944297 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444059901231 / 20000000000000 : ℝ))
      (E := (cell12963 ⟨13, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41810209944297 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (444059901231 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_14 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41792923797519 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555075880083 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨14, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41792923797519 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555075880083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_15 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (2610978114439 / 3125000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220307496333 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨15, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (2610978114439 / 3125000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220307496333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_16 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16703355211153 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555077888893 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨16, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16703355211153 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555077888893 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_17 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (41741138371251 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555078882061 / 25000000000000 : ℝ))
      (E := (cell12963 ⟨17, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (41741138371251 / 50000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (555078882061 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_18 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (20861950422187 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110159767651 / 50000000000000 : ℝ))
      (E := (cell12963 ⟨18, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (20861950422187 / 25000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (1110159767651 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12963_19 : CellCertificate 12963 (27483946765679 / 312500000000000 : ℝ) (405081551139351 / 250000000000000000 : ℝ) (327140263636057 / 10000000000000000 : ℝ)
    (cell12963 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · norm_num [cell12963]
  · have h := gap_lower (n := 12963) (a := (16682670172233 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220323522809 / 100000000000000 : ℝ))
      (E := (cell12963 ⟨19, by decide⟩).energy) (xi := (327140263636057 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12963 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12963]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12963])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12963) (a := (16682670172233 / 20000000000000 : ℝ)) (b := (158859883291 / 100000000000000 : ℝ)) (q := (2220323522809 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12963])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12963]

theorem cert12964_0 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (42036038864547 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220132303039 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨0, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (42036038864547 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220132303039 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_1 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (1680743717903 / 2000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110068160537 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨1, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (1680743717903 / 2000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110068160537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_2 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (42001159438993 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555035082273 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨2, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (42001159438993 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555035082273 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_3 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83967476641359 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220144335477 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨3, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83967476641359 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220144335477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_4 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83932659149217 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220148348357 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨4, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83932659149217 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220148348357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_5 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83897866365699 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110076187801 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨5, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83897866365699 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110076187801 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_6 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (10482887281891 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110078183427 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨6, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (10482887281891 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110078183427 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_7 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41914177391009 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444032065881 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨7, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41914177391009 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444032065881 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_8 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83793635911067 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110082193171 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨8, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83793635911067 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110082193171 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_9 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83758941607157 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110084185229 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨9, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83758941607157 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110084185229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_10 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41862135917677 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220172346291 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨10, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41862135917677 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220172346291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_11 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (10461203320113 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555044094557 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨11, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (10461203320113 / 12500000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555044094557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_12 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83655005749237 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555045089037 / 25000000000000 : ℝ))
      (E := (cell12964 ⟨12, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83655005749237 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (555045089037 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_13 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83620409365961 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110092201029 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨13, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83620409365961 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110092201029 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_14 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (41792918688431 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277523550657 / 12500000000000 : ℝ))
      (E := (cell12964 ⟨14, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (41792918688431 / 50000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (277523550657 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_15 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (1305488902311 / 1562500000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220192370977 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨15, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (1305488902311 / 1562500000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220192370977 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_16 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83516766445227 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110098210319 / 50000000000000 : ℝ))
      (E := (cell12964 ⟨16, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83516766445227 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (1110098210319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_17 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83482267435147 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220200384429 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨17, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83482267435147 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220200384429 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_18 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83447792684153 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444040876661 / 20000000000000 : ℝ))
      (E := (cell12964 ⟨18, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83447792684153 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (444040876661 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12964_19 : CellCertificate 12964 (109932429867803 / 1250000000000000 : ℝ) (506312868033 / 312500000000000 : ℝ) (327114438563839 / 10000000000000000 : ℝ)
    (cell12964 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · norm_num [cell12964]
  · have h := gap_lower (n := 12964) (a := (83413342158907 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220208421609 / 100000000000000 : ℝ))
      (E := (cell12964 ⟨19, by decide⟩).energy) (xi := (327114438563839 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12964 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12964]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12964])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12964) (a := (83413342158907 / 100000000000000 : ℝ)) (b := (158847485979 / 100000000000000 : ℝ)) (q := (2220208421609 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12964])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12964]

theorem cert12965_0 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (42036031605813 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220017227907 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨0, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (42036031605813 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220017227907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_1 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (42018585843859 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (111001061287 / 5000000000000 : ℝ))
      (E := (cell12965 ⟨1, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (42018585843859 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (111001061287 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_2 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (84002304980151 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222002521427 / 10000000000000 : ℝ))
      (E := (cell12965 ⟨2, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (84002304980151 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222002521427 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_3 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16793492610537 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444005851957 / 20000000000000 : ℝ))
      (E := (cell12965 ⟨3, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16793492610537 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444005851957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_4 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83932645869269 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220033254621 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨4, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83932645869269 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220033254621 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_5 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83897853394041 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220037264533 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨5, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83897853394041 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220037264533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_6 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (2620721424729 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220041239159 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨6, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (2620721424729 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220041239159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_7 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41914171212821 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (138752827737 / 6250000000000 : ℝ))
      (E := (cell12965 ⟨7, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41914171212821 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (138752827737 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_8 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20948405965421 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220049227519 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨8, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20948405965421 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220049227519 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_9 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16751785972867 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277506656897 / 12500000000000 : ℝ))
      (E := (cell12965 ⟨9, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16751785972867 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (277506656897 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_10 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83724260398663 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220057275303 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨10, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83724260398663 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220057275303 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_11 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83689615429917 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220061294189 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨11, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83689615429917 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220061294189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_12 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (20913748730881 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220065259763 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨12, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (20913748730881 / 25000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220065259763 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_13 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (16724079769019 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222006929403 / 10000000000000 : ℝ))
      (E := (cell12965 ⟨13, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (16724079769019 / 20000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (222006929403 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_14 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (2612057098763 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110036643143 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨14, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (2612057098763 / 3125000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110036643143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_15 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83551279835453 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (138754831247 / 6250000000000 : ℝ))
      (E := (cell12965 ⟨15, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83551279835453 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (138754831247 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_16 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (83516756836347 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220081281883 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨16, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (83516756836347 / 100000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220081281883 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_17 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (41741129064707 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444017059013 / 20000000000000 : ℝ))
      (E := (cell12965 ⟨17, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (41741129064707 / 50000000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (444017059013 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_18 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (10430972960143 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220089285819 / 100000000000000 : ℝ))
      (E := (cell12965 ⟨18, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (10430972960143 / 12500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (2220089285819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12965_19 : CellCertificate 12965 (109929073169137 / 1250000000000000 : ℝ) (101254760634177 / 62500000000000000 : ℝ) (327088617606121 / 10000000000000000 : ℝ)
    (cell12965 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · norm_num [cell12965]
  · have h := gap_lower (n := 12965) (a := (417066667291 / 500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110046658349 / 50000000000000 : ℝ))
      (E := (cell12965 ⟨19, by decide⟩).energy) (xi := (327088617606121 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12965 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12965]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12965])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12965) (a := (417066667291 / 500000000000 : ℝ)) (b := (15883509061 / 10000000000000 : ℝ)) (q := (1110046658349 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12965])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12965]

theorem cert12966_0 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (84072048696401 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443980429671 / 20000000000000 : ℝ))
      (E := (cell12966 ⟨0, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (84072048696401 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443980429671 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_1 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (8403715748249 / 10000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109953063013 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨1, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (8403715748249 / 10000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109953063013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_2 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16800458216897 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554977538247 / 25000000000000 : ℝ))
      (E := (cell12966 ⟨2, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16800458216897 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554977538247 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_3 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83967449466143 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219914179787 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨3, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83967449466143 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219914179787 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_4 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (10491579073927 / 12500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219918156617 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨4, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (10491579073927 / 12500000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219918156617 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_5 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (41948920212221 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219922149233 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨5, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (41948920212221 / 50000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219922149233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_6 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83863072929549 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (8671586583 / 390625000000 : ℝ))
      (E := (cell12966 ⟨6, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83863072929549 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (8671586583 / 390625000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_7 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83828330071251 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277491269253 / 12500000000000 : ℝ))
      (E := (cell12966 ⟨7, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83828330071251 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (277491269253 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_8 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83793611814249 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (138745886289 / 6250000000000 : ℝ))
      (E := (cell12966 ⟨8, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83793611814249 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (138745886289 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_9 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (3350356724937 / 4000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (110996909693 / 5000000000000 : ℝ))
      (E := (cell12966 ⟨9, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (3350356724937 / 4000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (110996909693 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_10 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83724248963849 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (221994220027 / 10000000000000 : ℝ))
      (E := (cell12966 ⟨10, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83724248963849 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (221994220027 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_11 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (2615300134399 / 3125000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443989241229 / 20000000000000 : ℝ))
      (E := (cell12966 ⟨11, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (2615300134399 / 3125000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (443989241229 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_12 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83654984099613 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219950217527 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨12, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83654984099613 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219950217527 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_13 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (16724077665199 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (221995418207 / 10000000000000 : ℝ))
      (E := (cell12966 ⟨13, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (16724077665199 / 20000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (221995418207 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_14 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83585816945701 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219958221583 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨14, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83585816945701 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219958221583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_15 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83551269924697 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554990556267 / 25000000000000 : ℝ))
      (E := (cell12966 ⟨15, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83551269924697 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554990556267 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_16 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (668133977833 / 800000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109983098759 / 50000000000000 : ℝ))
      (E := (cell12966 ⟨16, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (668133977833 / 800000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (1109983098759 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_17 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83482248825303 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554992550479 / 25000000000000 : ℝ))
      (E := (cell12966 ⟨17, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83482248825303 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (554992550479 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_18 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83447774679721 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219974242843 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨18, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83447774679721 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219974242843 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12966_19 : CellCertificate 12966 (879405735732821 / 10000000000000000 : ℝ) (404987795469159 / 250000000000000000 : ℝ) (65412560152371 / 2000000000000000 : ℝ)
    (cell12966 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · norm_num [cell12966]
  · have h := gap_lower (n := 12966) (a := (83413324759043 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219978208077 / 100000000000000 : ℝ))
      (E := (cell12966 ⟨19, by decide⟩).energy) (xi := (65412560152371 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12966 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12966]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12966])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12966) (a := (83413324759043 / 100000000000000 : ℝ)) (b := (31764539437 / 20000000000000 : ℝ)) (q := (2219978208077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12966])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12966]

theorem cert12967_0 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (84072034183417 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443957412877 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨0, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (84072034183417 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443957412877 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_1 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (21009285819867 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219791079791 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨1, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (21009285819867 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219791079791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_2 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (42001138595493 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554948771841 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨2, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (42001138595493 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554948771841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_3 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (20991858970433 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554949773871 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨3, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (20991858970433 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554949773871 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_4 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (10491577414457 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219803112277 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨4, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (10491577414457 / 12500000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219803112277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_5 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (838978274569 / 1000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219807087657 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨5, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (838978274569 / 1000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219807087657 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_6 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83863060269791 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443962217429 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨6, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83863060269791 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443962217429 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_7 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (20957079429711 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109907559051 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨7, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (20957079429711 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109907559051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_8 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83793599768761 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219819129613 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨8, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83793599768761 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219819129613 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_9 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41879453192213 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443964625693 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨9, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41879453192213 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443964625693 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_10 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (20931059382727 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219827121197 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨10, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (20931059382727 / 25000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219827121197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_11 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83689593173457 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219831114097 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨11, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83689593173457 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219831114097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_12 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16730994655501 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109917556603 / 50000000000000 : ℝ))
      (E := (cell12967 ⟨12, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16730994655501 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (1109917556603 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_13 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83620377808661 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (13873994527 / 625000000000 : ℝ))
      (E := (cell12967 ⟨13, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83620377808661 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (13873994527 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_14 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16717161346543 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219843152989 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨14, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16717161346543 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219843152989 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_15 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (41775630007817 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219847146329 / 100000000000000 : ℝ))
      (E := (cell12967 ⟨15, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (41775630007817 / 50000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (2219847146329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_16 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83516737623561 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (277481395943 / 12500000000000 : ℝ))
      (E := (cell12967 ⟨16, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83516737623561 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (277481395943 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_17 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83482239522813 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (110992758161 / 5000000000000 : ℝ))
      (E := (cell12967 ⟨17, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83482239522813 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (110992758161 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_18 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (83447765679883 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443971827573 / 20000000000000 : ℝ))
      (E := (cell12967 ⟨18, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (83447765679883 / 100000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (443971827573 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12967_19 : CellCertificate 12967 (879378890080677 / 10000000000000000 : ℝ) (809913106445273 / 500000000000000000 : ℝ) (65407397605999 / 2000000000000000 : ℝ)
    (cell12967 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · norm_num [cell12967]
  · have h := gap_lower (n := 12967) (a := (16682663212287 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554965788507 / 25000000000000 : ℝ))
      (E := (cell12967 ⟨19, by decide⟩).energy) (xi := (65407397605999 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12967 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12967]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12967])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12967) (a := (16682663212287 / 20000000000000 : ℝ)) (b := (158810305703 / 100000000000000 : ℝ)) (q := (554965788507 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12967])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12967]

theorem cert12968_0 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (42036009836337 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443934406767 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨0, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (42036009836337 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443934406767 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_1 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (84037129078649 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219676029177 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨1, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (84037129078649 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219676029177 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_2 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (42001131649827 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109840037641 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨2, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (42001131649827 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109840037641 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_3 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83967422299451 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443936812957 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨3, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83967422299451 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443936812957 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_4 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83932606041991 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221968806367 / 10000000000000 : ℝ))
      (E := (cell12968 ⟨4, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83932606041991 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (221968806367 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_5 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (16779562898283 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109846039903 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨5, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (16779562898283 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109846039903 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_6 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83863047612053 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554924015707 / 25000000000000 : ℝ))
      (E := (cell12968 ⟨6, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83863047612053 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (554924015707 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_7 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83828305368421 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109850039013 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨7, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83828305368421 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109850039013 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_8 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83793587725221 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443940814897 / 20000000000000 : ℝ))
      (E := (cell12968 ⟨8, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83793587725221 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (443940814897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_9 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41879447323669 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219708058991 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨9, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41879447323669 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219708058991 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_10 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83724226099843 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219712096151 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨10, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83724226099843 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219712096151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_11 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (16737916409597 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219716076137 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨11, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (16737916409597 / 20000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219716076137 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_12 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41827481228599 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (34683126893 / 1562500000000 : ℝ))
      (E := (cell12968 ⟨12, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41827481228599 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (34683126893 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_13 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (20905091823273 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219724120781 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨13, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (20905091823273 / 25000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219724120781 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_14 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (41792898260729 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219728080501 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨14, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (41792898260729 / 50000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219728080501 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_15 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10443906263533 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219732121921 / 100000000000000 : ℝ))
      (E := (cell12968 ⟨15, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10443906263533 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (2219732121921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_16 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (83516728019653 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277467016719 / 12500000000000 : ℝ))
      (E := (cell12968 ⟨16, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (83516728019653 / 100000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277467016719 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_17 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (10435278777743 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109870060371 / 50000000000000 : ℝ))
      (E := (cell12968 ⟨17, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (10435278777743 / 12500000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (1109870060371 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_18 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (8344775668163 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277468018207 / 12500000000000 : ℝ))
      (E := (cell12968 ⟨18, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (8344775668163 / 10000000000000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277468018207 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12968_19 : CellCertificate 12968 (879352048395741 / 10000000000000000 : ℝ) (1619701263184101 / 1000000000000000000 : ℝ) (327011179409493 / 10000000000000000 : ℝ)
    (cell12968 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · norm_num [cell12968]
  · have h := gap_lower (n := 12968) (a := (40729153987 / 48828125000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277468519319 / 12500000000000 : ℝ))
      (E := (cell12968 ⟨19, by decide⟩).energy) (xi := (327011179409493 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12968 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12968]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12968])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12968) (a := (40729153987 / 48828125000 : ℝ)) (b := (39699479041 / 25000000000000 : ℝ)) (q := (277468519319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12968])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12968]

theorem cert12969_0 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (21018001291043 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109778528353 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨0, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (21018001291043 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109778528353 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_1 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (42018557440017 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109780516023 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨1, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (42018557440017 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109780516023 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_2 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (8400224941049 / 10000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219565058859 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨2, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (8400224941049 / 10000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219565058859 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_3 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (839674087193 / 1000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219569029783 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨3, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (839674087193 / 1000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219569029783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_4 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41966296385209 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219573068729 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨4, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41966296385209 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219573068729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_5 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83897801527987 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219577067727 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨5, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83897801527987 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219577067727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_6 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (16772606991267 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109790546149 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨6, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (16772606991267 / 20000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109790546149 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_7 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41914146509991 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109792545899 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨7, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41914146509991 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109792545899 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_8 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (20948393920907 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109794536633 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨8, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (20948393920907 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109794536633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_9 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83758882912161 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219593101533 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨9, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83758882912161 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219593101533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_10 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83724214670651 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109798533533 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨10, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83724214670651 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109798533533 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_11 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (1673791418487 / 2000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219601092269 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨11, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (1673791418487 / 2000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219601092269 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_12 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (20913737909673 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277450633377 / 12500000000000 : ℝ))
      (E := (cell12969 ⟨12, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (20913737909673 / 25000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (277450633377 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_13 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (10452544597411 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219609113313 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨13, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (10452544597411 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219609113313 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_14 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83585786311931 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219613120449 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨14, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83585786311931 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219613120449 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_15 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (83551240202587 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219617093659 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨15, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (83551240202587 / 100000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219617093659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_16 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41758359208701 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109810548071 / 50000000000000 : ℝ))
      (E := (cell12969 ⟨16, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41758359208701 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (1109810548071 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_17 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (10435277615337 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219625132717 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨17, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (10435277615337 / 12500000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219625132717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_18 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41723873842481 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219629149703 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨18, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41723873842481 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219629149703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12969_19 : CellCertificate 12969 (879325210677091 / 10000000000000000 : ℝ) (40489408318821 / 25000000000000000 : ℝ) (326985374899303 / 10000000000000000 : ℝ)
    (cell12969 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · norm_num [cell12969]
  · have h := gap_lower (n := 12969) (a := (41706649335433 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219633151369 / 100000000000000 : ℝ))
      (E := (cell12969 ⟨19, by decide⟩).energy) (xi := (326985374899303 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12969 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12969]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12969])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12969) (a := (41706649335433 / 50000000000000 : ℝ)) (b := (158785528567 / 100000000000000 : ℝ)) (q := (2219633151369 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12969])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12969]

theorem cert12970_0 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (8407199065791 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109721037581 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨0, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (8407199065791 / 10000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109721037581 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_1 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (84037100683623 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219446030537 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨1, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (84037100683623 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219446030537 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_2 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (21000558880873 / 25000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219450038097 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨2, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (21000558880873 / 25000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219450038097 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_3 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83967395141279 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109727024193 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨3, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83967395141279 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109727024193 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_4 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83932579500939 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554864517381 / 25000000000000 : ℝ))
      (E := (cell12970 ⟨4, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83932579500939 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (554864517381 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_5 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (16779557713323 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219462051423 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨5, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (16779557713323 / 20000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219462051423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_6 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83863022302637 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219466059603 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨6, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83863022302637 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219466059603 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_7 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (3353131226941 / 4000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (110973505071 / 5000000000000 : ℝ))
      (E := (cell12970 ⟨7, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (3353131226941 / 4000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (110973505071 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_8 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83793563643981 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109737033967 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨8, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83793563643981 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109737033967 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_9 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83758871178893 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109739040977 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨9, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83758871178893 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109739040977 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_10 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83724203243333 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219482092013 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨10, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83724203243333 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219482092013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_11 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83689559802553 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219486104399 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨11, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83689559802553 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219486104399 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_12 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83654940821987 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (44389802503 / 2000000000000 : ℝ))
      (E := (cell12970 ⟨12, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83654940821987 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (44389802503 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_13 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83620346267249 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219494101919 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨13, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83620346267249 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219494101919 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_14 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83585776104131 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443899619669 / 20000000000000 : ℝ))
      (E := (cell12970 ⟨14, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83585776104131 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (443899619669 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_15 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (41775615149301 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219502119731 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨15, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (41775615149301 / 50000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219502119731 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_16 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83516708816807 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (69359566029 / 3125000000000 : ℝ))
      (E := (cell12970 ⟨16, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83516708816807 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (69359566029 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_17 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83482211625067 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109755070457 / 50000000000000 : ℝ))
      (E := (cell12970 ⟨17, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83482211625067 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (1109755070457 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_18 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (83447738689877 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221951415001 / 10000000000000 : ℝ))
      (E := (cell12970 ⟨18, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (83447738689877 / 100000000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (221951415001 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12970_19 : CellCertificate 12970 (175859675384761 / 2000000000000000 : ℝ) (1619451421592301 / 1000000000000000000 : ℝ) (163479787249189 / 5000000000000000 : ℝ)
    (cell12970 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · norm_num [cell12970]
  · have h := gap_lower (n := 12970) (a := (5213330623619 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219518144481 / 100000000000000 : ℝ))
      (E := (cell12970 ⟨19, by decide⟩).energy) (xi := (163479787249189 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12970 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12970]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12970])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12970) (a := (5213330623619 / 6250000000000 : ℝ)) (b := (158773142911 / 100000000000000 : ℝ)) (q := (2219518144481 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12970])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12970]

theorem cert12971_0 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (84071976153887 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443865417841 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨0, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (84071976153887 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443865417841 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_1 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (42018543244707 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219331082513 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨1, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (42018543244707 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219331082513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_2 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (84002221638659 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443867025753 / 20000000000000 : ℝ))
      (E := (cell12971 ⟨2, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (84002221638659 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (443867025753 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_3 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83967381565387 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554834780149 / 25000000000000 : ℝ))
      (E := (cell12971 ⟨3, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83967381565387 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554834780149 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_4 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (5245785389597 / 6250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109671561993 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨4, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (5245785389597 / 6250000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109671561993 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_5 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41948887803649 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138709193053 / 6250000000000 : ℝ))
      (E := (cell12971 ⟨5, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41948887803649 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138709193053 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_6 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41931504825479 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109675569337 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨6, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41931504825479 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109675569337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_7 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (1676565366581 / 2000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554838776723 / 25000000000000 : ℝ))
      (E := (cell12971 ⟨7, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (1676565366581 / 2000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (554838776723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_8 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (2094838790157 / 2500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (69354972391 / 3125000000000 : ℝ))
      (E := (cell12971 ⟨8, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (2094838790157 / 2500000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (69354972391 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_9 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (16751771889507 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277420389543 / 12500000000000 : ℝ))
      (E := (cell12971 ⟨9, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (16751771889507 / 20000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277420389543 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_10 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83724191817887 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109683556461 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨10, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83724191817887 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109683556461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_11 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (2615298396331 / 3125000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138710694533 / 6250000000000 : ℝ))
      (E := (cell12971 ⟨11, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (2615298396331 / 3125000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (138710694533 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_12 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83654930007083 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219375121203 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨12, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83654930007083 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219375121203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_13 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (41810167878487 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109689572369 / 50000000000000 : ℝ))
      (E := (cell12971 ⟨13, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (41810167878487 / 50000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (1109689572369 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_14 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (4179288294903 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219383130513 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨14, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (4179288294903 / 5000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219383130513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_15 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83551220396309 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (44387742839 / 2000000000000 : ℝ))
      (E := (cell12971 ⟨15, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83551220396309 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (44387742839 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_16 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (20879174804467 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219391184107 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨16, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (20879174804467 / 25000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219391184107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_17 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83482202329059 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219395145331 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨17, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83482202329059 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219395145331 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_18 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (83447729696377 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219399146573 / 100000000000000 : ℝ))
      (E := (cell12971 ⟨18, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (83447729696377 / 100000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (2219399146573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12971_19 : CellCertificate 12971 (879271547134961 / 10000000000000000 : ℝ) (404831632424507 / 250000000000000000 : ℝ) (326933778205673 / 10000000000000000 : ℝ)
    (cell12971 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · norm_num [cell12971]
  · have h := gap_lower (n := 12971) (a := (8341328128649 / 10000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277425399021 / 12500000000000 : ℝ))
      (E := (cell12971 ⟨19, by decide⟩).energy) (xi := (326933778205673 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12971 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12971]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12971])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12971) (a := (8341328128649 / 10000000000000 : ℝ)) (b := (158760759197 / 100000000000000 : ℝ)) (q := (277425399021 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12971])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12971]

theorem cert12972_0 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (84071961652103 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219212156673 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨0, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (84071961652103 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219212156673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_1 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (84037072006623 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219216189457 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨1, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (84037072006623 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219216189457 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_2 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (21000551793709 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554805039883 / 25000000000000 : ℝ))
      (E := (cell12972 ⟨2, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (21000551793709 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554805039883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_3 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83967367120509 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219224191017 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨3, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83967367120509 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219224191017 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_4 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16786510361519 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109614088121 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨4, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16786510361519 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109614088121 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_5 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83897761200239 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219232180957 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨5, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83897761200239 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219232180957 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_6 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83862995262773 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109618077397 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨6, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83862995262773 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109618077397 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_7 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83828253959717 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (13870251019 / 625000000000 : ℝ))
      (E := (cell12972 ⟨7, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83828253959717 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (13870251019 / 625000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_8 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (41896768627887 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109622106401 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨8, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (41896768627887 / 50000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109622106401 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_9 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83758845115833 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219248194839 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨9, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83758845115833 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219248194839 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_10 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83724177504967 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554813043421 / 25000000000000 : ℝ))
      (E := (cell12972 ⟨10, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83724177504967 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (554813043421 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_11 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83689534388429 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219256213719 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨11, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83689534388429 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219256213719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_12 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16730983146331 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109630102407 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨12, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16730983146331 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109630102407 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_13 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83620321500259 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219264210833 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨13, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83620321500259 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219264210833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_14 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83585751660033 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219268237323 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨14, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83585751660033 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219268237323 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_15 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (20887801544237 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219272231397 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨15, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (20887801544237 / 25000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219272231397 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_16 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (1670333700343 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109638128127 / 50000000000000 : ℝ))
      (E := (cell12972 ⟨16, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (1670333700343 / 2000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (1109638128127 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_17 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83482188146961 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219280258477 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨17, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83482188146961 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219280258477 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_18 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (83447715532877 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221928424257 / 10000000000000 : ℝ))
      (E := (cell12972 ⟨18, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (83447715532877 / 100000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (221928424257 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12972_19 : CellCertificate 12972 (879244721309639 / 10000000000000000 : ℝ) (809600828532781 / 500000000000000000 : ℝ) (163453993010071 / 5000000000000000 : ℝ)
    (cell12972 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · norm_num [cell12972]
  · have h := gap_lower (n := 12972) (a := (16682653428313 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219288271081 / 100000000000000 : ℝ))
      (E := (cell12972 ⟨19, by decide⟩).energy) (xi := (163453993010071 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12972 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12972]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12972])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12972) (a := (16682653428313 / 20000000000000 : ℝ)) (b := (158748377423 / 100000000000000 : ℝ)) (q := (2219288271081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12972])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12972]

theorem cert12973_0 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (42035973576279 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219097219729 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨0, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (42035973576279 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219097219729 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_1 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (42018528756757 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109550623343 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨1, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (42018528756757 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109550623343 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_2 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (84002192688159 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219105268863 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨2, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (84002192688159 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219105268863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_3 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83967352640257 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221910923673 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨3, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83967352640257 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221910923673 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_4 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83932537333763 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219113274199 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨4, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83932537333763 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219113274199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_5 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83897746732821 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109558636649 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨5, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83897746732821 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109558636649 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_6 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83862980801763 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443824248313 / 20000000000000 : ℝ))
      (E := (cell12973 ⟨6, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83862980801763 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (443824248313 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_7 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83828239505109 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219125244289 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨7, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83828239505109 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219125244289 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_8 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41896761403781 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (17336947567 / 781250000000 : ℝ))
      (E := (cell12973 ⟨8, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41896761403781 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (17336947567 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_9 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83758830674013 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219133265183 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨9, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83758830674013 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219133265183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_10 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (20931040767383 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219137296717 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨10, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (20931040767383 / 25000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219137296717 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_11 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41844759979687 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109570636673 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨11, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41844759979687 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109570636673 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_12 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41827450654487 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221914531727 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨12, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41827450654487 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221914531727 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_13 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41810153541973 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (277393664759 / 12500000000000 : ℝ))
      (E := (cell12973 ⟨13, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41810153541973 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (277393664759 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_14 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41792868625041 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109576640613 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨14, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41792868625041 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109576640613 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_15 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16710238354671 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219157328339 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨15, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16710238354671 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219157328339 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_16 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (83516670619909 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219161289907 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨16, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (83516670619909 / 100000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219161289907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_17 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41741086878033 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219165345309 / 100000000000000 : ℝ))
      (E := (cell12973 ⟨17, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41741086878033 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (2219165345309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_18 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (41723850574161 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109584662209 / 50000000000000 : ℝ))
      (E := (cell12973 ⟨18, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (41723850574161 / 50000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (1109584662209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12973_19 : CellCertificate 12973 (879217899446917 / 10000000000000000 : ℝ) (1619076803690449 / 1000000000000000000 : ℝ) (326882197940741 / 10000000000000000 : ℝ)
    (cell12973 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · norm_num [cell12973]
  · have h := gap_lower (n := 12973) (a := (16682650552669 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221917334799 / 10000000000000 : ℝ))
      (E := (cell12973 ⟨19, by decide⟩).energy) (xi := (326882197940741 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12973 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12973]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12973])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12973) (a := (16682650552669 / 20000000000000 : ℝ)) (b := (15873599759 / 10000000000000 : ℝ)) (q := (221917334799 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12973])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12973]

theorem cert12974_0 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (84071932655251 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554745584053 / 25000000000000 : ℝ))
      (E := (cell12974 ⟨0, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (84071932655251 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554745584053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_1 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (84037043022643 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443797271473 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨1, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (84037043022643 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443797271473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_2 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (42001089101859 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109495186893 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨2, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (42001089101859 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109495186893 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_3 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (262397931757 / 312500000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554748598463 / 25000000000000 : ℝ))
      (E := (cell12974 ⟨3, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (262397931757 / 312500000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554748598463 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_4 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16786504572433 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2218998367751 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨4, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16786504572433 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2218998367751 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_5 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20974433066909 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219002361233 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨5, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20974433066909 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219002361233 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_6 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16772593268597 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221900638191 / 10000000000000 : ℝ))
      (E := (cell12974 ⟨6, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16772593268597 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221900638191 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_7 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20957056263183 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (17336018587 / 781250000000 : ℝ))
      (E := (cell12974 ⟨7, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20957056263183 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (17336018587 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_8 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83793508361581 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219014359947 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨8, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83793508361581 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219014359947 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_9 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83758816234421 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109509194587 / 50000000000000 : ℝ))
      (E := (cell12974 ⟨9, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83758816234421 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (1109509194587 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_10 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (3348965945453 / 4000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (44380448307 / 2000000000000 : ℝ))
      (E := (cell12974 ⟨10, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (3348965945453 / 4000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (44380448307 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_11 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16737901106509 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554756596667 / 25000000000000 : ℝ))
      (E := (cell12974 ⟨11, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16737901106509 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (554756596667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_12 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (41827443444259 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219030425329 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨12, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (41827443444259 / 50000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219030425329 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_13 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83620292669857 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219034420913 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨13, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83620292669857 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219034420913 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_14 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (20896430710589 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (110951921853 / 5000000000000 : ℝ))
      (E := (cell12974 ⟨14, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (20896430710589 / 25000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (110951921853 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_15 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16710235474397 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443808484177 / 20000000000000 : ℝ))
      (E := (cell12974 ⟨15, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16710235474397 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (443808484177 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_16 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83516656224889 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219046435587 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨16, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83516656224889 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219046435587 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_17 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (2608817480231 / 3125000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219050427747 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨17, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (2608817480231 / 3125000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219050427747 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_18 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (83447686765987 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221905446013 / 10000000000000 : ℝ))
      (E := (cell12974 ⟨18, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (83447686765987 / 100000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (221905446013 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

theorem cert12974_19 : CellCertificate 12974 (7033528652367 / 80000000000000 : ℝ) (1618951969568233 / 1000000000000000000 : ℝ) (13074256558657 / 400000000000000 : ℝ)
    (cell12974 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · norm_num [cell12974]
  · have h := gap_lower (n := 12974) (a := (16682647677469 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219058420507 / 100000000000000 : ℝ))
      (E := (cell12974 ⟨19, by decide⟩).energy) (xi := (13074256558657 / 400000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12974 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12974]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12974])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12974) (a := (16682647677469 / 20000000000000 : ℝ)) (b := (9920226231 / 6250000000000 : ℝ)) (q := (2219058420507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12974])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12974]

end BstLean.Part268
