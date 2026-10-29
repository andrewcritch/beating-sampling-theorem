import BstLean.Part268CellShard13Data

/-! Twenty scalar cells per dimension in a 25-dimension shard. -/
namespace BstLean.Part268
open Real BstLean.Part263

theorem cert12675_0 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (42038184697451 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563637138139 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨0, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (42038184697451 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563637138139 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_1 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (84041386382597 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254552587551 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨1, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (84041386382597 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254552587551 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_2 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (328150110609 / 390625000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254556571453 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨2, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (328150110609 / 390625000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254556571453 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_3 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10496436894787 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17613754461 / 781250000000 : ℝ))
      (E := (cell12675 ⟨3, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10496436894787 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17613754461 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_4 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41968293436719 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450912918979 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨4, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41968293436719 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450912918979 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_5 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20975425856297 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (281821074201 / 12500000000000 : ℝ))
      (E := (cell12675 ⟨5, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20975425856297 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (281821074201 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_6 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83866844777593 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254572575241 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨6, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83866844777593 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254572575241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_7 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10479001361861 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450915309527 / 20000000000000 : ℝ))
      (E := (cell12675 ⟨7, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10479001361861 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (450915309527 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_8 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83797201741497 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140911286023 / 6250000000000 : ℝ))
      (E := (cell12675 ⟨8, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83797201741497 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140911286023 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_9 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (83762417282029 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254584552807 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨9, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (83762417282029 / 100000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254584552807 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_10 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (261648929629 / 312500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127294271001 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨10, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (261648929629 / 312500000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127294271001 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_11 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20923230576057 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17614004303 / 781250000000 : ℝ))
      (E := (cell12675 ⟨11, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20923230576057 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17614004303 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_12 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (41829105858017 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127298292867 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨12, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (41829105858017 / 50000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127298292867 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_13 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (2090588142051 / 2500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17614067149 / 781250000000 : ℝ))
      (E := (cell12675 ⟨13, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (2090588142051 / 2500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (17614067149 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_14 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20897216041943 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563651146203 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨14, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20897216041943 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563651146203 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_15 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (8355422713893 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254608560723 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨15, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (8355422713893 / 10000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254608560723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_16 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16703922912279 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140913286657 / 6250000000000 : ℝ))
      (E := (cell12675 ⟨16, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16703922912279 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (140913286657 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_17 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (10435628300153 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127308275559 / 50000000000000 : ℝ))
      (E := (cell12675 ⟨17, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (10435628300153 / 12500000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (1127308275559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_18 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (20862615656163 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563655143991 / 25000000000000 : ℝ))
      (E := (cell12675 ⟨18, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (20862615656163 / 25000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (563655143991 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12675_19 : CellCertificate 12675 (887390288570421 / 10000000000000000 : ℝ) (33143104260069 / 20000000000000000 : ℝ) (83688365477403 / 2500000000000000 : ℝ)
    (cell12675 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · norm_num [cell12675]
  · have h := gap_lower (n := 12675) (a := (16683184639617 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254624549413 / 100000000000000 : ℝ))
      (E := (cell12675 ⟨19, by decide⟩).energy) (xi := (83688365477403 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12675 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12675]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12675])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12675) (a := (16683184639617 / 20000000000000 : ℝ)) (b := (2031414591 / 1250000000000 : ℝ)) (q := (2254624549413 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12675])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12675]

theorem cert12676_0 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (16815270841403 / 20000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127212486143 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨0, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (16815270841403 / 20000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127212486143 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_1 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (42020685757867 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563607242963 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨1, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (42020685757867 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563607242963 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_2 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (21001603442403 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254432978909 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨2, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (21001603442403 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254432978909 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_3 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83971480932121 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254437002393 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨3, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83971480932121 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254437002393 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_4 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (5246035810433 / 6250000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254440993081 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨4, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (5246035810433 / 6250000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254440993081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_5 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20975422459473 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127222479661 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨5, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20975422459473 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127222479661 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_6 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83866831509061 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563612241789 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨6, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83866831509061 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563612241789 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_7 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83831997944671 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254452966521 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨7, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83831997944671 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254452966521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_8 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41898594554573 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254456965001 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨8, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41898594554573 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254456965001 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_9 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (41881202483549 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254460969927 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨9, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (41881202483549 / 50000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254460969927 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_10 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83727645483321 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127232494189 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨10, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83727645483321 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127232494189 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_11 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20923227655699 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127234484559 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨11, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20923227655699 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127234484559 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_12 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (16731640070137 / 20000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (450894595349 / 20000000000000 : ℝ))
      (E := (cell12676 ⟨12, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (16731640070137 / 20000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (450894595349 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_13 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (20905878658083 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127238479739 / 50000000000000 : ℝ))
      (E := (cell12676 ⟨13, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (20905878658083 / 25000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (1127238479739 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_14 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (4179442671663 / 5000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254480981467 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨14, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (4179442671663 / 5000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254480981467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_15 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83554216719173 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254484990391 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨15, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83554216719173 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254484990391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_16 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83519604455953 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254488991773 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨16, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83519604455953 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254488991773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_17 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83485016609657 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563623247723 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨17, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83485016609657 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563623247723 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_18 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83450453146521 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254496992783 / 100000000000000 : ℝ))
      (E := (cell12676 ⟨18, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83450453146521 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (2254496992783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12676_19 : CellCertificate 12676 (887362248039349 / 10000000000000000 : ℝ) (66280977528967 / 40000000000000000 : ℝ) (10460200200167 / 312500000000000 : ℝ)
    (cell12676 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · norm_num [cell12676]
  · have h := gap_lower (n := 12676) (a := (83415914032951 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563625250561 / 25000000000000 : ℝ))
      (E := (cell12676 ⟨19, by decide⟩).energy) (xi := (10460200200167 / 312500000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12676 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12676]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12676])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12676) (a := (83415914032951 / 100000000000000 : ℝ)) (b := (40625047419 / 25000000000000 : ℝ)) (q := (563625250561 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12676])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12676]

theorem cert12677_0 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (42038169510763 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254301445073 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨0, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (42038169510763 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254301445073 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_1 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (2626292395351 / 3125000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (281788176159 / 12500000000000 : ℝ))
      (E := (cell12677 ⟨1, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (2626292395351 / 3125000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (281788176159 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_2 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (2100159980641 / 2500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563577359887 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨2, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (2100159980641 / 2500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563577359887 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_3 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (20992866677057 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127156714573 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨3, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (20992866677057 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127156714573 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_4 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41968279531331 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (70447420143 / 3125000000000 : ℝ))
      (E := (cell12677 ⟨4, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41968279531331 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (70447420143 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_5 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83901676252801 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563580359083 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨5, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83901676252801 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563580359083 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_6 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41933409121347 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254325412507 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨6, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41933409121347 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254325412507 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_7 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (4191599249829 / 5000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254329438907 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨7, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (4191599249829 / 5000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254329438907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_8 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83797176478883 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563583351799 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨8, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83797176478883 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563583351799 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_9 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16752478530843 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254337440673 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨9, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16752478530843 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254337440673 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_10 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83727633487373 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (704481697 / 31250000000 : ℝ))
      (E := (cell12677 ⟨10, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83727633487373 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (704481697 / 31250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_11 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83692898943337 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254345441203 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨11, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83692898943337 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254345441203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_12 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (8365818898727 / 10000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225434942157 / 10000000000000 : ℝ))
      (E := (cell12677 ⟨12, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (8365818898727 / 10000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (225434942157 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_13 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (41811751792259 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254353435873 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨13, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (41811751792259 / 50000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254353435873 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_14 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (20897210675151 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254357432063 / 100000000000000 : ℝ))
      (E := (cell12677 ⟨14, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (20897210675151 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (2254357432063 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_15 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (16710841260247 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127180707951 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨15, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (16710841260247 / 20000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127180707951 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_16 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83519594352291 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127182725549 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨16, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83519594352291 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127182725549 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_17 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (10435625852479 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563592356647 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨17, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (10435625852479 / 12500000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563592356647 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_18 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (83450443670093 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563593351391 / 25000000000000 : ℝ))
      (E := (cell12677 ⟨18, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (83450443670093 / 100000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (563593351391 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12677_19 : CellCertificate 12677 (22183355293917 / 250000000000000 : ℝ) (1656893684083513 / 1000000000000000000 : ℝ) (334699355336829 / 10000000000000000 : ℝ)
    (cell12677 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · norm_num [cell12677]
  · have h := gap_lower (n := 12677) (a := (20853976217371 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127188725537 / 50000000000000 : ℝ))
      (E := (cell12677 ⟨19, by decide⟩).energy) (xi := (334699355336829 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12677 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12677]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12677])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12677) (a := (20853976217371 / 25000000000000 : ℝ)) (b := (162487214159 / 100000000000000 : ℝ)) (q := (1127188725537 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12677])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12677]

theorem cert12678_0 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (21019080959609 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254177913107 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨0, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (21019080959609 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254177913107 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_1 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (2626291930909 / 3125000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563545474953 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨1, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (2626291930909 / 3125000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563545474953 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_2 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (84006384683989 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254185895513 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨2, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (84006384683989 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254185895513 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_3 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (10496431560827 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450837981829 / 20000000000000 : ℝ))
      (E := (cell12678 ⟨3, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (10496431560827 / 12500000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450837981829 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_4 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83936545160637 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (56354847287 / 2500000000000 : ℝ))
      (E := (cell12678 ⟨4, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83936545160637 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (56354847287 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_5 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83901662669913 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254197908791 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨5, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83901662669913 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254197908791 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_6 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20966701244623 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254201911293 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨6, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20966701244623 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254201911293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_7 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16766394410123 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254205906819 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨7, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16766394410123 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254205906819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_8 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83797163850707 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127104951477 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨8, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83797163850707 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127104951477 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_9 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83762380343381 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (90168556281 / 4000000000000 : ℝ))
      (E := (cell12678 ⟨9, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83762380343381 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (90168556281 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_10 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41863810746717 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254217926111 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨10, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41863810746717 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254217926111 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_11 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83692887265849 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254221908973 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨11, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83692887265849 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254221908973 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_12 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20914544406447 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254225920209 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨12, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20914544406447 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254225920209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_13 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41811746269299 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127114954017 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨13, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41811746269299 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127114954017 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_14 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (16717766393961 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254233936597 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨14, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (16717766393961 / 20000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254233936597 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_15 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (41777097942557 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (281779736927 / 12500000000000 : ℝ))
      (E := (cell12678 ⟨15, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (41777097942557 / 50000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (281779736927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_16 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83519584250409 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127120953153 / 50000000000000 : ℝ))
      (E := (cell12678 ⟨16, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83519584250409 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (1127120953153 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_17 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (20871249257937 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254245916411 / 100000000000000 : ℝ))
      (E := (cell12678 ⟨17, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (20871249257937 / 25000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (2254245916411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_18 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83450434195369 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563562482691 / 25000000000000 : ℝ))
      (E := (cell12678 ⟨18, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83450434195369 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (563562482691 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12678_19 : CellCertificate 12678 (887306179721403 / 10000000000000000 : ℝ) (1656762950576577 / 1000000000000000000 : ℝ) (334672308702881 / 10000000000000000 : ℝ)
    (cell12678 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · norm_num [cell12678]
  · have h := gap_lower (n := 12678) (a := (83415895707681 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450850779181 / 20000000000000 : ℝ))
      (E := (cell12678 ⟨19, by decide⟩).energy) (xi := (334672308702881 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12678 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12678]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12678])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12678) (a := (83415895707681 / 100000000000000 : ℝ)) (b := (16247424073 / 10000000000000 : ℝ)) (q := (450850779181 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12678])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12678]

theorem cert12679_0 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16815261731549 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254054434197 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨0, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16815261731549 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254054434197 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_1 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10505165866163 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (140878652717 / 6250000000000 : ℝ))
      (E := (cell12679 ⟨1, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10505165866163 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (140878652717 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_2 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (42003185072329 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127031231259 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨2, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (42003185072329 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127031231259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_3 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16794287653457 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254066442391 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨3, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16794287653457 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254066442391 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_4 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16787306252171 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450814089919 / 20000000000000 : ℝ))
      (E := (cell12679 ⟨4, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16787306252171 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (450814089919 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_5 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20975412272307 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (35219913041 / 1562500000000 : ℝ))
      (E := (cell12679 ⟨5, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20975412272307 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (35219913041 / 1562500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_6 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16773358343291 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254078405567 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨6, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16773358343291 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254078405567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_7 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10478994888347 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281760303529 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨7, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10478994888347 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281760303529 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_8 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41898575612309 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (90163458091 / 4000000000000 : ℝ))
      (E := (cell12679 ⟨8, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41898575612309 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (90163458091 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_9 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16752473606919 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563522606751 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨9, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16752473606919 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563522606751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_10 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41863804750753 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254094417469 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨10, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41863804750753 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254094417469 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_11 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20923218897583 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (70440575953 / 3125000000000 : ℝ))
      (E := (cell12679 ⟨11, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20923218897583 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (70440575953 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_12 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83658166266239 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254102414573 / 100000000000000 : ℝ))
      (E := (cell12679 ⟨12, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83658166266239 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (2254102414573 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_13 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (83623481494573 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281763304259 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨13, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (83623481494573 / 100000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281763304259 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_14 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41794410620431 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281763804617 / 12500000000000 : ℝ))
      (E := (cell12679 ⟨14, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41794410620431 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (281763804617 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_15 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20888546367703 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563528607233 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨15, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20888546367703 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563528607233 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_16 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (41759787075153 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (112705920779 / 5000000000000 : ℝ))
      (E := (cell12679 ⟨16, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (41759787075153 / 50000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (112705920779 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_17 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (16696997449081 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563530615091 / 25000000000000 : ℝ))
      (E := (cell12679 ⟨17, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (16696997449081 / 20000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (563530615091 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_18 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (20862606180587 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (90165058077 / 4000000000000 : ℝ))
      (E := (cell12679 ⟨18, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (20862606180587 / 25000000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (90165058077 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12679_19 : CellCertificate 12679 (443639075966253 / 5000000000000000 : ℝ) (414158059424621 / 250000000000000000 : ℝ) (334645266502311 / 10000000000000000 : ℝ)
    (cell12679 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · norm_num [cell12679]
  · have h := gap_lower (n := 12679) (a := (10426985818443 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127065226621 / 50000000000000 : ℝ))
      (E := (cell12679 ⟨19, by decide⟩).energy) (xi := (334645266502311 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12679 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12679]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12679])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12679) (a := (10426985818443 / 12500000000000 : ℝ)) (b := (40615317347 / 25000000000000 : ℝ)) (q := (1127065226621 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12679])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12679]

theorem cert12680_0 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (84076293479451 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253931008347 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨0, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (84076293479451 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253931008347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_1 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (42020656035939 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253934982423 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨1, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (42020656035939 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253934982423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_2 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (84006355607647 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253938966999 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨2, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (84006355607647 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253938966999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_3 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16794284810047 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (17608929461 / 781250000000 : ℝ))
      (E := (cell12680 ⟨3, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16794284810047 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (17608929461 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_4 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41968258681657 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126973501561 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨4, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41968258681657 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126973501561 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_5 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16780327102149 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253951013833 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨5, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16780327102149 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253951013833 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_6 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83866778456581 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225395501123 / 10000000000000 : ℝ))
      (E := (cell12680 ⟨6, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83866778456581 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225395501123 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_7 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83831946165061 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563489750787 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨7, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83831946165061 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563489750787 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_8 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16759427720123 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126981498583 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨8, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16759427720123 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126981498583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_9 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83762355727857 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253967000611 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨9, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83762355727857 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253967000611 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_10 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41863798755793 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126985481259 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨10, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41863798755793 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126985481259 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_11 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (16738572783357 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126987502887 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨11, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (16738572783357 / 20000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126987502887 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_12 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83658154908621 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563494740689 / 25000000000000 : ℝ))
      (E := (cell12680 ⟨12, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83658154908621 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (563494740689 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_13 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41811735226221 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225398301399 / 10000000000000 : ℝ))
      (E := (cell12680 ⟨13, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41811735226221 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (225398301399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_14 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41794405256887 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253986991219 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨14, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41794405256887 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253986991219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_15 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41777087529163 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450798203291 / 20000000000000 : ℝ))
      (E := (cell12680 ⟨15, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41777087529163 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (450798203291 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_16 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (41759782025991 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126997489461 / 50000000000000 : ℝ))
      (E := (cell12680 ⟨16, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (41759782025991 / 50000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (1126997489461 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_17 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83484977460803 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253999000241 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨17, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83484977460803 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2253999000241 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_18 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (83450415251029 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254002969051 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨18, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (83450415251029 / 100000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254002969051 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12680_19 : CellCertificate 12680 (887250128388977 / 10000000000000000 : ℝ) (1617677290473 / 976562500000000 : ℝ) (66923645746787 / 2000000000000000 : ℝ)
    (cell12680 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · norm_num [cell12680]
  · have h := gap_lower (n := 12680) (a := (8341587738907 / 10000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254007006583 / 100000000000000 : ℝ))
      (E := (cell12680 ⟨19, by decide⟩).energy) (xi := (66923645746787 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12680 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12680]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12680])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12680) (a := (8341587738907 / 10000000000000 : ℝ)) (b := (40612075033 / 25000000000000 : ℝ)) (q := (2254007006583 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12680])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12680]

theorem cert12681_0 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (42038139151777 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563451894437 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨0, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (42038139151777 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563451894437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_1 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (8404129721681 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253811574497 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨1, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (8404129721681 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253811574497 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_2 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (42003170536477 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253815582521 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨2, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (42003170536477 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253815582521 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_3 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16794281967093 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126909776437 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨3, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16794281967093 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126909776437 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_4 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41968251734007 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112691177603 / 5000000000000 : ℝ))
      (E := (cell12681 ⟨4, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41968251734007 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112691177603 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_5 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (16780324386893 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253827588493 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨5, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (16780324386893 / 20000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253827588493 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_6 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (8386676519887 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563457888609 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨6, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (8386676519887 / 10000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563457888609 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_7 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (163734244581 / 195312500000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126917786797 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨7, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (163734244581 / 195312500000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126917786797 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_8 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41898562989349 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253839595623 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨8, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41898562989349 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253839595623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_9 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (41881171711583 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253843569829 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨9, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (41881171711583 / 50000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253843569829 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_10 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (3349103420947 / 4000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112692378063 / 5000000000000 : ℝ))
      (E := (cell12681 ⟨10, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (3349103420947 / 4000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (112692378063 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_11 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83692852245209 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253851576741 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨11, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83692852245209 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253851576741 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_12 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (10457267944117 / 12500000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563463891189 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨12, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (10457267944117 / 12500000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563463891189 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_13 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (20905864853051 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563464897419 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨13, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (20905864853051 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563464897419 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_14 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83588799788541 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563465899861 / 25000000000000 : ℝ))
      (E := (cell12681 ⟨14, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83588799788541 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (563465899861 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_15 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83554164647657 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253867599823 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨15, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83554164647657 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253867599823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_16 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (20879888488859 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253871596333 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨16, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (20879888488859 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253871596333 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_17 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83484967677941 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253875594249 / 100000000000000 : ℝ))
      (E := (cell12681 ⟨17, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83484967677941 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (2253875594249 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_18 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (20862601445353 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (11269397993 / 500000000000 : ℝ))
      (E := (cell12681 ⟨18, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (20862601445353 / 25000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (11269397993 / 500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12681_19 : CellCertificate 12681 (887222109089807 / 10000000000000000 : ℝ) (16563708738093 / 10000000000000000 : ℝ) (83647798849141 / 2500000000000000 : ℝ)
    (cell12681 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · norm_num [cell12681]
  · have h := gap_lower (n := 12681) (a := (83415868232261 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126941777963 / 50000000000000 : ℝ))
      (E := (cell12681 ⟨19, by decide⟩).energy) (xi := (83647798849141 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12681 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12681]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12681])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12681) (a := (83415868232261 / 100000000000000 : ℝ)) (b := (81217666481 / 50000000000000 : ℝ)) (q := (1126941777963 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12681])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12681]

theorem cert12682_0 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (84076263130053 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253684200211 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨0, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (84076263130053 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253684200211 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_1 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (84041282364099 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253688219697 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨1, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (84041282364099 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253688219697 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_2 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (84006326540579 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126846096689 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨2, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (84006326540579 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126846096689 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_3 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83971395622973 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126848093997 / 50000000000000 : ℝ))
      (E := (cell12682 ⟨3, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83971395622973 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (1126848093997 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_4 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41968244787477 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281712526527 / 12500000000000 : ℝ))
      (E := (cell12682 ⟨4, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41968244787477 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281712526527 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_5 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41950804180193 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563426054133 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨5, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41950804180193 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563426054133 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_6 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41933375971661 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281713526129 / 12500000000000 : ℝ))
      (E := (cell12682 ⟨6, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41933375971661 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281713526129 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_7 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41915960144003 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450742439509 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨7, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41915960144003 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450742439509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_8 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83797113358867 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563429047413 / 25000000000000 : ℝ))
      (E := (cell12682 ⟨8, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83797113358867 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (563429047413 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_9 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41881165560261 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253720192677 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨9, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41881165560261 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253720192677 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_10 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20931893384443 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450744842739 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨10, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20931893384443 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450744842739 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_11 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41846420287801 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281716025183 / 12500000000000 : ℝ))
      (E := (cell12682 ⟨11, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41846420287801 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (281716025183 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_12 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83658132199181 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70429131893 / 3125000000000 : ℝ))
      (E := (cell12682 ⟨12, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83658132199181 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70429131893 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_13 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (41811724186929 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450747243849 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨13, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (41811724186929 / 50000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450747243849 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_14 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83588789065163 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253740203479 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨14, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83588789065163 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253740203479 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_15 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20888538559701 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253744179041 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨15, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20888538559701 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253744179041 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_16 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20879885965167 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70429631551 / 3125000000000 : ℝ))
      (E := (cell12682 ⟨16, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20879885965167 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (70429631551 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_17 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83484957896819 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253752184183 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨17, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83484957896819 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253752184183 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_18 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (83450396313497 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450751244823 / 20000000000000 : ℝ))
      (E := (cell12682 ⟨18, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (83450396313497 / 100000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (450751244823 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12682_19 : CellCertificate 12682 (13862407719281 / 156250000000000 : ℝ) (1656240222788449 / 1000000000000000000 : ℝ) (66912833297803 / 2000000000000000 : ℝ)
    (cell12682 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · norm_num [cell12682]
  · have h := gap_lower (n := 12682) (a := (20853964769279 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253760217779 / 100000000000000 : ℝ))
      (E := (cell12682 ⟨19, by decide⟩).energy) (xi := (66912833297803 / 2000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12682 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12682]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12682])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12682) (a := (20853964769279 / 25000000000000 : ℝ)) (b := (162422367877 / 100000000000000 : ℝ)) (q := (2253760217779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12682])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12682]

theorem cert12683_0 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (21019061989737 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281695109467 / 12500000000000 : ℝ))
      (E := (cell12683 ⟨0, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (21019061989737 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281695109467 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_1 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16808253502749 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (225356486019 / 10000000000000 : ℝ))
      (E := (cell12683 ⟨1, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16808253502749 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (225356486019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_2 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (42003156005261 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253568857423 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨2, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (42003156005261 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253568857423 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_3 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83971381412761 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450714575273 / 20000000000000 : ℝ))
      (E := (cell12683 ⟨3, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83971381412761 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450714575273 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_4 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16787295136827 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281697108473 / 12500000000000 : ℝ))
      (E := (cell12683 ⟨4, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16787295136827 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281697108473 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_5 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (20975398697127 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (90143233601 / 4000000000000 : ℝ))
      (E := (cell12683 ⟨5, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (20975398697127 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (90143233601 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_6 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83866738689937 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (28169810739 / 1250000000000 : ℝ))
      (E := (cell12683 ⟨6, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83866738689937 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (28169810739 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_7 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83831907352663 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126794437501 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨7, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83831907352663 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126794437501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_8 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (32733242477 / 39062500000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126796447623 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨8, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (32733242477 / 39062500000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126796447623 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_9 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83762318819923 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126798434579 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨9, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83762318819923 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126798434579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_10 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (20931890388469 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253600861783 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨10, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (20931890388469 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253600861783 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_11 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16738565781593 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450720975989 / 20000000000000 : ℝ))
      (E := (cell12683 ⟨11, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16738565781593 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (450720975989 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_12 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83658120847357 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253608872127 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨12, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83658120847357 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253608872127 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_13 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (16724687467481 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281701605573 / 12500000000000 : ℝ))
      (E := (cell12683 ⟨13, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (16724687467481 / 20000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (281701605573 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_14 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41794389171819 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (112680843073 / 5000000000000 : ℝ))
      (E := (cell12683 ⟨14, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41794389171819 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (112680843073 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_15 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (41777071915883 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253620870427 / 100000000000000 : ℝ))
      (E := (cell12683 ⟨15, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (41777071915883 / 50000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (2253620870427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_16 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83519533767677 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126812438501 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨16, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83519533767677 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126812438501 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_17 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (20871237029359 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126814443229 / 50000000000000 : ℝ))
      (E := (cell12683 ⟨17, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (20871237029359 / 25000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (1126814443229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_18 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83450386847283 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563408211399 / 25000000000000 : ℝ))
      (E := (cell12683 ⟨18, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83450386847283 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (563408211399 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12683_19 : CellCertificate 12683 (887166083220499 / 10000000000000000 : ℝ) (1656109592376921 / 1000000000000000000 : ℝ) (167268571005051 / 5000000000000000 : ℝ)
    (cell12683 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · norm_num [cell12683]
  · have h := gap_lower (n := 12683) (a := (83415849923633 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (56340921891 / 2500000000000 : ℝ))
      (E := (cell12683 ⟨19, by decide⟩).energy) (xi := (167268571005051 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12683 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12683]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12683])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12683) (a := (83415849923633 / 100000000000000 : ℝ)) (b := (162409404877 / 100000000000000 : ℝ)) (q := (56340921891 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12683])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12683]

theorem cert12684_0 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (42038116395119 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253437546517 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨0, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (42038116395119 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253437546517 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_1 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (84041252665747 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253441553811 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨1, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (84041252665747 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253441553811 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_2 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (84006297482783 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253445574659 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨2, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (84006297482783 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253445574659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_3 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83971367204827 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (140840597507 / 6250000000000 : ℝ))
      (E := (cell12684 ⟨3, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83971367204827 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (140840597507 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_4 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41968230897777 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (70420424271 / 3125000000000 : ℝ))
      (E := (cell12684 ⟨4, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41968230897777 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (70420424271 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_5 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83901581218831 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253457574823 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨5, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83901581218831 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253457574823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_6 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83866725438713 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126730781327 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨6, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83866725438713 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126730781327 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_7 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20957973604861 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253465547993 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨7, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20957973604861 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253465547993 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_8 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83797088125457 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126734769209 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨8, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83797088125457 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126734769209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_9 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83762306521371 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563368385313 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨9, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83762306521371 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563368385313 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_10 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (20931887392997 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253477563567 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨10, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (20931887392997 / 25000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253477563567 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_11 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (10461602155287 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253481554119 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨11, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (10461602155287 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253481554119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_12 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (10457263687183 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (901394231 / 40000000000 : ℝ))
      (E := (cell12684 ⟨12, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (10457263687183 / 12500000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (901394231 / 40000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_13 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83623426302843 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253489581921 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨13, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83623426302843 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253489581921 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_14 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (83588767623967 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563373393347 / 25000000000000 : ℝ))
      (E := (cell12684 ⟨14, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (83588767623967 / 100000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (563373393347 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_15 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (5222133339159 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253497557663 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨15, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (5222133339159 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253497557663 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_16 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (5219970229779 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253501540261 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨16, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (5219970229779 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253501540261 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_17 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (5217808646237 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126752792331 / 50000000000000 : ℝ))
      (E := (cell12684 ⟨17, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (5217808646237 / 6250000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (1126752792331 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_18 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (8345037738277 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (140844348719 / 6250000000000 : ℝ))
      (E := (cell12684 ⟨18, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (8345037738277 / 10000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (140844348719 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12684_19 : CellCertificate 12684 (44356903832417 / 500000000000000 : ℝ) (20699737282123 / 12500000000000000 : ℝ) (334510121958641 / 10000000000000000 : ℝ)
    (cell12684 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · norm_num [cell12684]
  · have h := gap_lower (n := 12684) (a := (41707920385907 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253513587759 / 100000000000000 : ℝ))
      (E := (cell12684 ⟨19, by decide⟩).energy) (xi := (334510121958641 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12684 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12684]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12684])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12684) (a := (41707920385907 / 50000000000000 : ℝ)) (b := (162396443961 / 100000000000000 : ℝ)) (q := (2253513587759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12684])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12684]

theorem cert12685_0 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (84076217623923 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253314328173 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨0, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (84076217623923 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253314328173 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_1 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16808247564021 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253318300561 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨1, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16808247564021 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253318300561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_2 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (1050078536967 / 1250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (17604080369 / 781250000000 : ℝ))
      (E := (cell12685 ⟨2, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (1050078536967 / 1250000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (17604080369 / 781250000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_3 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (8397135299917 / 10000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563331574279 / 25000000000000 : ℝ))
      (E := (cell12685 ⟨3, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (8397135299917 / 10000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (563331574279 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_4 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (20984111977303 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140833142561 / 6250000000000 : ℝ))
      (E := (cell12685 ⟨4, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (20984111977303 / 25000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140833142561 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_5 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83901567651353 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (56333357627 / 2500000000000 : ℝ))
      (E := (cell12685 ⟨5, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83901567651353 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (56333357627 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_6 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (1677334243793 / 2000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253338319633 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨6, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (1677334243793 / 2000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253338319633 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_7 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83831881488347 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126671137247 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨7, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83831881488347 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126671137247 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_8 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83797075511879 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126673146579 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨8, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83797075511879 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126673146579 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_9 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (2617571694527 / 3125000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (90134013 / 4000000000 : ℝ))
      (E := (cell12685 ⟨9, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (2617571694527 / 3125000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (90134013 / 4000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_10 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41863768796053 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253354319049 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨10, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41863768796053 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253354319049 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_11 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (16738561115719 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126679141027 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨11, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (16738561115719 / 20000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126679141027 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_12 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (167316196299 / 200000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253362278607 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨12, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (167316196299 / 200000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253362278607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_13 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83623415270173 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253366315031 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨13, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83623415270173 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253366315031 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_14 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83588756906149 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253370281129 / 100000000000000 : ℝ))
      (E := (cell12685 ⟨14, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83588756906149 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (2253370281129 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_15 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83554123023137 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (225337429891 / 10000000000000 : ℝ))
      (E := (cell12685 ⟨15, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83554123023137 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (225337429891 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_16 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83519513587027 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126689157889 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨16, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83519513587027 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126689157889 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_17 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (83484928563887 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450676455759 / 20000000000000 : ℝ))
      (E := (cell12685 ⟨17, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (83484928563887 / 100000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (450676455759 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_18 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (41725183959979 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126693154691 / 50000000000000 : ℝ))
      (E := (cell12685 ⟨18, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (41725183959979 / 50000000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (1126693154691 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12685_19 : CellCertificate 12685 (887110074316499 / 10000000000000000 : ℝ) (413962098340583 / 250000000000000000 : ℝ) (41810388291681 / 1250000000000000 : ℝ)
    (cell12685 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · norm_num [cell12685]
  · have h := gap_lower (n := 12685) (a := (10426978952707 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140836893493 / 6250000000000 : ℝ))
      (E := (cell12685 ⟨19, by decide⟩).energy) (xi := (41810388291681 / 1250000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12685 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12685]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12685])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12685) (a := (10426978952707 / 12500000000000 : ℝ)) (b := (20297935641 / 12500000000000 : ℝ)) (q := (140836893493 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12685])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12685]

theorem cert12686_0 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (84076202460003 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563297761819 / 25000000000000 : ℝ))
      (E := (cell12686 ⟨0, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (84076202460003 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (563297761819 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_1 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (42020611488409 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (140824690163 / 6250000000000 : ℝ))
      (E := (cell12686 ⟨1, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (42020611488409 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (140824690163 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_2 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (84006268434253 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253199052999 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨2, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (84006268434253 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253199052999 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_3 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83971338795791 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (18025624699 / 800000000000 : ℝ))
      (E := (cell12686 ⟨3, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83971338795791 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (18025624699 / 800000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_4 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83936434025109 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253207038599 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨4, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83936434025109 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253207038599 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_5 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (3356062163443 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253211088719 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨5, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (3356062163443 / 4000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253211088719 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_6 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83866698942747 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225321507211 / 10000000000000 : ℝ))
      (E := (cell12686 ⟨6, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83866698942747 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225321507211 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_7 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (20957967139843 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253219054503 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨7, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (20957967139843 / 25000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253219054503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_8 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83797062900383 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (90128921739 / 4000000000000 : ℝ))
      (E := (cell12686 ⟨8, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83797062900383 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (90128921739 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_9 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83762281930401 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450645409269 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨9, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83762281930401 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450645409269 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_10 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83727525614231 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126615535093 / 50000000000000 : ℝ))
      (E := (cell12686 ⟨10, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83727525614231 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1126615535093 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_11 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83692793916861 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1802588051 / 80000000000 : ℝ))
      (E := (cell12686 ⟨11, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83692793916861 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (1802588051 / 80000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_12 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (16731617360693 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253239091627 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨12, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (16731617360693 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253239091627 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_13 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (41811702119697 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450648608783 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨13, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (41811702119697 / 50000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450648608783 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_14 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83588746190183 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253247042819 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨14, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83588746190183 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253247042819 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_15 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (10444264077693 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225325109417 / 10000000000000 : ℝ))
      (E := (cell12686 ⟨15, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (10444264077693 / 12500000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (225325109417 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_16 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83519503499367 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450651017437 / 20000000000000 : ℝ))
      (E := (cell12686 ⟨16, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83519503499367 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (450651017437 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_17 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83484918789719 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253259085273 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨17, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83484918789719 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253259085273 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_18 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (16690071691769 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253263093459 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨18, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (16690071691769 / 20000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253263093459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12686_19 : CellCertificate 12686 (887082076223967 / 10000000000000000 : ℝ) (1655717824749523 / 1000000000000000000 : ℝ) (16722804756667 / 500000000000000 : ℝ)
    (cell12686 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · norm_num [cell12686]
  · have h := gap_lower (n := 12686) (a := (83415822473161 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253267058277 / 100000000000000 : ℝ))
      (E := (cell12686 ⟨19, by decide⟩).energy) (xi := (16722804756667 / 500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12686 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12686]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12686])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12686) (a := (83415822473161 / 100000000000000 : ℝ)) (b := (162370528379 / 100000000000000 : ℝ)) (q := (2253267058277 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12686])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12686]

theorem cert12687_0 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (3363047491939 / 4000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253067877257 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨0, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (3363047491939 / 4000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253067877257 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_1 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16808241627177 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (112653594781 / 5000000000000 : ℝ))
      (E := (cell12687 ⟨1, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16808241627177 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (112653594781 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_2 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (84006253913461 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (56326896799 / 2500000000000 : ℝ))
      (E := (cell12687 ⟨2, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (84006253913461 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (56326896799 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_3 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (164006493349 / 195312500000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253079873013 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨3, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (164006493349 / 195312500000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253079873013 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_4 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83936420143243 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (281635481193 / 12500000000000 : ℝ))
      (E := (cell12687 ⟨4, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83936420143243 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (281635481193 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_5 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20975385130749 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450617573563 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨5, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20975385130749 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450617573563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_6 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16773337139601 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253091878033 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨6, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16773337139601 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253091878033 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_7 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41915927816259 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (281636986003 / 12500000000000 : ℝ))
      (E := (cell12687 ⟨7, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41915927816259 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (281636986003 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_8 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (8379705029097 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450619969473 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨8, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (8379705029097 / 10000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450619969473 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_9 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41881134818991 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253103879347 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨9, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41881134818991 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253103879347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_10 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83727513638361 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126553937511 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨10, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83727513638361 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126553937511 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_11 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (16738556451419 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253111899209 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨11, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (16738556451419 / 20000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253111899209 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_12 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83658075459359 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253115842293 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨12, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83658075459359 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253115842293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_13 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41811696605253 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126559942399 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨13, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41811696605253 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126559942399 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_14 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83588735476069 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (112656192923 / 5000000000000 : ℝ))
      (E := (cell12687 ⟨14, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83588735476069 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (112656192923 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_15 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (20888525555441 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253127885283 / 100000000000000 : ℝ))
      (E := (cell12687 ⟨15, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (20888525555441 / 25000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (2253127885283 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_16 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (41759746706741 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450626370897 / 20000000000000 : ℝ))
      (E := (cell12687 ⟨16, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (41759746706741 / 50000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (450626370897 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_17 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83484909017289 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126567943841 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨17, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83484909017289 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126567943841 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_18 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (10431293624929 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126569936753 / 50000000000000 : ℝ))
      (E := (cell12687 ⟨18, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (10431293624929 / 12500000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (1126569936753 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12687_19 : CellCertificate 12687 (443527041184867 / 5000000000000000 : ℝ) (1655587276726543 / 1000000000000000000 : ℝ) (334429088357133 / 10000000000000000 : ℝ)
    (cell12687 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · norm_num [cell12687]
  · have h := gap_lower (n := 12687) (a := (83415813326327 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225314387493 / 10000000000000 : ℝ))
      (E := (cell12687 ⟨19, by decide⟩).energy) (xi := (334429088357133 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12687 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12687]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12687])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12687) (a := (83415813326327 / 100000000000000 : ℝ)) (b := (162357573713 / 100000000000000 : ℝ)) (q := (225314387493 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12687])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12687]

theorem cert12688_0 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (84076172139341 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126472351249 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨0, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (84076172139341 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126472351249 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_1 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (84041193297307 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252948686099 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨1, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (84041193297307 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252948686099 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_2 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (16801247878997 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126476343131 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨2, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (16801247878997 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126476343131 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_3 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83971310395861 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (281619588989 / 12500000000000 : ℝ))
      (E := (cell12688 ⟨3, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83971310395861 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (281619588989 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_4 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41968203131807 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563240178453 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨4, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41968203131807 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563240178453 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_5 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (16780305392423 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (22529647003 / 1000000000000 : ℝ))
      (E := (cell12688 ⟨5, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (16780305392423 / 20000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (22529647003 / 1000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_6 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83866672455423 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126484368703 / 50000000000000 : ℝ))
      (E := (cell12688 ⟨6, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83866672455423 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (1126484368703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_7 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41915921353893 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563243179271 / 25000000000000 : ℝ))
      (E := (cell12688 ⟨7, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41915921353893 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (563243179271 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_8 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (2094925942091 / 2500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252976704831 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨8, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (2094925942091 / 2500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252976704831 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_9 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (10470282168451 / 12500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252980707967 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨9, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (10470282168451 / 12500000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252980707967 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_10 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (5232968854031 / 6250000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252984733561 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨10, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (5232968854031 / 6250000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252984733561 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_11 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (653849770307 / 781250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (450597746073 / 20000000000000 : ℝ))
      (E := (cell12688 ⟨11, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (653849770307 / 781250000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (450597746073 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_12 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83658064117181 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252992704877 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨12, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83658064117181 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252992704877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_13 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83623382183507 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252996721461 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨13, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83623382183507 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2252996721461 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_14 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (2612147648869 / 3125000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253000728053 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨14, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (2612147648869 / 3125000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253000728053 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_15 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (83554091823799 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253004730411 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨15, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (83554091823799 / 100000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253004730411 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_16 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20879870832343 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70406522939 / 3125000000000 : ℝ))
      (E := (cell12688 ⟨16, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20879870832343 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (70406522939 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_17 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (20871224811649 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (90120507441 / 4000000000000 : ℝ))
      (E := (cell12688 ⟨17, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (20871224811649 / 25000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (90120507441 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_18 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41725169770859 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253016707757 / 100000000000000 : ℝ))
      (E := (cell12688 ⟨18, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41725169770859 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (2253016707757 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12688_19 : CellCertificate 12688 (887026092752791 / 10000000000000000 : ℝ) (41386418732213 / 25000000000000000 : ℝ) (167201043001823 / 5000000000000000 : ℝ)
    (cell12688 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · norm_num [cell12688]
  · have h := gap_lower (n := 12688) (a := (41707902090577 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (450604137519 / 20000000000000 : ℝ))
      (E := (cell12688 ⟨19, by decide⟩).energy) (xi := (167201043001823 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12688 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12688]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12688])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12688) (a := (41707902090577 / 50000000000000 : ℝ)) (b := (20293077641 / 12500000000000 : ℝ)) (q := (450604137519 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12688])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12688]

theorem cert12689_0 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (84076156982599 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225282158081 / 10000000000000 : ℝ))
      (E := (cell12689 ⟨0, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (84076156982599 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (225282158081 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_1 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (84041178461081 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450565117509 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨1, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (84041178461081 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450565117509 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_2 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (42003112439411 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126414805809 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨2, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (42003112439411 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126414805809 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_3 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (8397129619931 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252833604071 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨3, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (8397129619931 / 10000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252833604071 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_4 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41968196193111 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126418786751 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨4, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41968196193111 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126418786751 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_5 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (10487689175429 / 12500000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252841586171 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨5, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (10487689175429 / 12500000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252841586171 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_6 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83866659214999 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252845592281 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨6, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83866659214999 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252845592281 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_7 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83831829785173 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126424799829 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨7, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83831829785173 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126424799829 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_8 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83797025078391 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252853557877 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨8, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83797025078391 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252853557877 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_9 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20940561264819 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252857590227 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨9, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20940561264819 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252857590227 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_10 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (20931872423159 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252861587759 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨10, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (20931872423159 / 25000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252861587759 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_11 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83692758943463 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112643277861 / 5000000000000 : ℝ))
      (E := (cell12689 ⟨11, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83692758943463 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (112643277861 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_12 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83658052776931 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252869563199 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨12, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83658052776931 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252869563199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_13 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83623371158397 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126436806007 / 50000000000000 : ℝ))
      (E := (cell12689 ⟨13, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83623371158397 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (1126436806007 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_14 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83588714053397 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252877593463 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨14, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83588714053397 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252877593463 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_15 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41777040713823 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450576314279 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨15, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41777040713823 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450576314279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_16 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (83519473247037 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450577121901 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨16, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (83519473247037 / 100000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450577121901 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_17 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (2087122236941 / 2500000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450577919343 / 20000000000000 : ℝ))
      (E := (cell12689 ⟨17, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (2087122236941 / 2500000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (450577919343 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_18 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41725165042851 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563223399053 / 25000000000000 : ℝ))
      (E := (cell12689 ⟨18, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41725165042851 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (563223399053 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12689_19 : CellCertificate 12689 (886998107372131 / 10000000000000000 : ℝ) (1655326242430587 / 1000000000000000000 : ℝ) (167187544035849 / 5000000000000000 : ℝ)
    (cell12689 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · norm_num [cell12689]
  · have h := gap_lower (n := 12689) (a := (41707897518821 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252897612779 / 100000000000000 : ℝ))
      (E := (cell12689 ⟨19, by decide⟩).energy) (xi := (167187544035849 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12689 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12689]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12689])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12689) (a := (41707897518821 / 50000000000000 : ℝ)) (b := (259730673 / 160000000000 : ℝ)) (q := (2252897612779 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12689])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12689]

theorem cert12690_0 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (84076141828249 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252698512193 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨0, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (84076141828249 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252698512193 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_1 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (84041163627209 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252702484293 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨1, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (84041163627209 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252702484293 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_2 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (42003105182487 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252706474459 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨2, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (42003105182487 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252706474459 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_3 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83971282005033 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563177622903 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨3, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83971282005033 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563177622903 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_4 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83936378511067 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (450542897303 / 20000000000000 : ℝ))
      (E := (cell12690 ⟨4, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83936378511067 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (450542897303 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_5 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41950749923473 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252718467503 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨5, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41950749923473 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252718467503 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_6 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41933322988367 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126361250303 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨6, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41933322988367 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126361250303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_7 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83831816864681 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563181619443 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨7, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83831816864681 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563181619443 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_8 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (10474626559403 / 12500000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252730464499 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨8, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (10474626559403 / 12500000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252730464499 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_9 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83762232772987 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126367234053 / 50000000000000 : ℝ))
      (E := (cell12690 ⟨9, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83762232772987 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (1126367234053 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_10 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (4186373886139 / 5000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252738495659 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨10, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (4186373886139 / 5000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252738495659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_11 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (20923186822399 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252742495907 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨11, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (20923186822399 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252742495907 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_12 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83658041438609 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563186618837 / 25000000000000 : ℝ))
      (E := (cell12690 ⟨12, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83658041438609 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (563186618837 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_13 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83623360135177 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252750498343 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨13, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83623360135177 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252750498343 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_14 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (83588703344837 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252754512827 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨14, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (83588703344837 / 100000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252754512827 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_15 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (41777035516653 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (450551693279 / 20000000000000 : ℝ))
      (E := (cell12690 ⟨15, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (41777035516653 / 50000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (450551693279 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_16 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (20879865791619 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252762480857 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨16, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (20879865791619 / 25000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252762480857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_17 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (4174243985521 / 5000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (112638325167 / 5000000000000 : ℝ))
      (E := (cell12690 ⟨17, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (4174243985521 / 5000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (112638325167 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_18 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (16690064126277 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252770480639 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨18, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (16690064126277 / 20000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252770480639 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12690_19 : CellCertificate 12690 (177394025245349 / 2000000000000000 : ℝ) (1655195756147877 / 1000000000000000000 : ℝ) (167174047280053 / 5000000000000000 : ℝ)
    (cell12690 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · norm_num [cell12690]
  · have h := gap_lower (n := 12690) (a := (8341578589579 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252774475721 / 100000000000000 : ℝ))
      (E := (cell12690 ⟨19, by decide⟩).energy) (xi := (167174047280053 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12690 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12690]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12690])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12690) (a := (8341578589579 / 10000000000000 : ℝ)) (b := (40579680551 / 25000000000000 : ℝ)) (q := (2252774475721 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12690])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12690]

theorem cert12691_0 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (84076126676291 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252575438841 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨0, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (84076126676291 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252575438841 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_1 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (84041148795689 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252579434179 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨1, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (84041148795689 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252579434179 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_2 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (84006195853439 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126291724179 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨2, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (84006195853439 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126291724179 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_3 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83971267813031 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126293716209 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨3, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83971267813031 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126293716209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_4 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41968182319073 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252591452857 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨4, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41968182319073 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252591452857 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_5 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83901486292657 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252595460153 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨5, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83901486292657 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252595460153 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_6 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83866632740627 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450519892477 / 20000000000000 : ℝ))
      (E := (cell12691 ⟨6, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83866632740627 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (450519892477 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_7 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (20957950986577 / 25000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252603409403 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨7, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (20957950986577 / 25000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252603409403 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_8 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83796999874137 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252607424703 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨8, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83796999874137 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252607424703 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_9 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (4188111024437 / 5000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (45052229153 / 2000000000000 : ℝ))
      (E := (cell12691 ⟨9, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (4188111024437 / 5000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (45052229153 / 2000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_10 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (5232966609683 / 6250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126307728633 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨10, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (5232966609683 / 6250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126307728633 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_11 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83692735637693 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252619430297 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨11, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83692735637693 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252619430297 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_12 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83658030102213 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225262344133 / 10000000000000 : ℝ))
      (E := (cell12691 ⟨12, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83658030102213 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225262344133 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_13 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16724669822769 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281578429821 / 12500000000000 : ℝ))
      (E := (cell12691 ⟨13, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16724669822769 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281578429821 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_14 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (5224293289883 / 6250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252631428011 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨14, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (5224293289883 / 6250000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252631428011 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_15 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (83554060640777 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281579426927 / 12500000000000 : ℝ))
      (E := (cell12691 ⟨15, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (83554060640777 / 100000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (281579426927 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_16 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (8351945308769 / 10000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126319732237 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨16, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (8351945308769 / 10000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126319732237 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_17 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (10435608743117 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225264346411 / 10000000000000 : ℝ))
      (E := (cell12691 ⟨17, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (10435608743117 / 12500000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (225264346411 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_18 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (16690062235753 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126323709637 / 50000000000000 : ℝ))
      (E := (cell12691 ⟨18, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (16690062235753 / 20000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (1126323709637 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12691_19 : CellCertificate 12691 (443471074657813 / 5000000000000000 : ℝ) (66202611617421 / 40000000000000000 : ℝ) (33432110546769 / 1000000000000000 : ℝ)
    (cell12691 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · norm_num [cell12691]
  · have h := gap_lower (n := 12691) (a := (41707888377799 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252651451187 / 100000000000000 : ℝ))
      (E := (cell12691 ⟨19, by decide⟩).energy) (xi := (33432110546769 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12691 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12691]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12691])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12691) (a := (41707888377799 / 50000000000000 : ℝ)) (b := (81152887931 / 50000000000000 : ℝ)) (q := (2252651451187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12691])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12691]

theorem cert12692_0 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (84076111526723 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252452418563 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨0, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (84076111526723 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252452418563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_1 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (2101028349163 / 2500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252456437203 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨1, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (2101028349163 / 2500000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252456437203 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_2 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (84006181344217 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1407787761 / 62500000000 : ℝ))
      (E := (cell12692 ⟨2, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (84006181344217 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1407787761 / 62500000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_3 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83971253623303 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281558053311 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨3, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83971253623303 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281558053311 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_4 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83936350767461 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252468414623 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨4, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83936350767461 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252468414623 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_5 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16780294548113 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (112623619517 / 5000000000000 : ℝ))
      (E := (cell12692 ⟨5, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16780294548113 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (112623619517 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_6 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41933309753339 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563119104917 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨6, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41933309753339 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563119104917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_7 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83831791030053 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281560049319 / 12500000000000 : ℝ))
      (E := (cell12692 ⟨7, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83831791030053 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (281560049319 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_8 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83796987275131 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450496887697 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨8, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83796987275131 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450496887697 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_9 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (16752441641307 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450497688563 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨9, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (16752441641307 / 20000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450497688563 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_10 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83727453789079 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126246207267 / 50000000000000 : ℝ))
      (E := (cell12692 ⟨10, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83727453789079 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (1126246207267 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_11 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20923180996939 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450499283691 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨11, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20923180996939 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450499283691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_12 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (653578271623 / 781250000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563125100763 / 25000000000000 : ℝ))
      (E := (cell12692 ⟨12, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (653578271623 / 781250000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (563125100763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_13 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41811669047201 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450500886537 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨13, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41811669047201 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450500886537 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_14 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20897170483317 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252508397151 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨14, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20897170483317 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252508397151 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_15 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83554050250061 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450502483691 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨15, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83554050250061 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450502483691 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_16 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83519443010677 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225251644399 / 10000000000000 : ℝ))
      (E := (cell12692 ⟨16, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83519443010677 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (225251644399 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_17 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (20871215045297 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (140782526301 / 6250000000000 : ℝ))
      (E := (cell12692 ⟨17, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (20871215045297 / 25000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (140782526301 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_18 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (83450301727843 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450504882423 / 20000000000000 : ℝ))
      (E := (cell12692 ⟨18, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (83450301727843 / 100000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (450504882423 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12692_19 : CellCertificate 12692 (886914176637767 / 10000000000000000 : ℝ) (1654934845288667 / 1000000000000000000 : ℝ) (33429412079327 / 1000000000000000 : ℝ)
    (cell12692 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · norm_num [cell12692]
  · have h := gap_lower (n := 12692) (a := (41707883808533 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252528422667 / 100000000000000 : ℝ))
      (E := (cell12692 ⟨19, by decide⟩).energy) (xi := (33429412079327 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12692 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12692]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12692])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12692) (a := (41707883808533 / 50000000000000 : ℝ)) (b := (162292831601 / 100000000000000 : ℝ)) (q := (2252528422667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12692])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12692]

theorem cert12693_0 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (16815219275909 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252329451361 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨0, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (16815219275909 / 20000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252329451361 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_1 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (84041119139703 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563083358883 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨1, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (84041119139703 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563083358883 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_2 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (84006166837307 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252337440047 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨2, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (84006166837307 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252337440047 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_3 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (10496404929481 / 12500000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (281542676993 / 12500000000000 : ℝ))
      (E := (cell12693 ⟨3, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (10496404929481 / 12500000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (281542676993 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_4 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (8393633689901 / 10000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126172714859 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨4, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (8393633689901 / 10000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126172714859 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_5 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20975364797667 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126174715923 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨5, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20975364797667 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126174715923 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_6 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41933303137443 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126176715203 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨6, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41933303137443 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126176715203 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_7 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41915889057959 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252357433219 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨7, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41915889057959 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252357433219 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_8 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20949243669551 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252361447853 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨8, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20949243669551 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252361447853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_9 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20940548981593 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563091355901 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨9, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20940548981593 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563091355901 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_10 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83727441825233 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (225236942551 / 10000000000000 : ℝ))
      (E := (cell12693 ⟨10, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83727441825233 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (225236942551 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_11 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83692712339783 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563093350579 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨11, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83692712339783 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563093350579 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_12 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (83658007435201 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252377418607 / 100000000000000 : ℝ))
      (E := (cell12693 ⟨12, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (83658007435201 / 100000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (2252377418607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_13 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41811663538423 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450476284517 / 20000000000000 : ℝ))
      (E := (cell12693 ⟨13, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41811663538423 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (450476284517 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_14 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41794335615129 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (9009541681 / 400000000000 : ℝ))
      (E := (cell12693 ⟨14, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41794335615129 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (9009541681 / 400000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_15 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20888509965289 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126194708677 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨15, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20888509965289 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126194708677 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_16 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (20879858233859 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126196709703 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨16, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (20879858233859 / 25000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126196709703 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_17 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41742425209587 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563099357917 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨17, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41742425209587 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563099357917 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_18 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (41725146139309 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563100364791 / 25000000000000 : ℝ))
      (E := (cell12693 ⟨18, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (41725146139309 / 50000000000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (563100364791 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12693_19 : CellCertificate 12693 (886886208192159 / 10000000000000000 : ℝ) (1654804420702439 / 1000000000000000000 : ℝ) (334267140535667 / 10000000000000000 : ℝ)
    (cell12693 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · norm_num [cell12693]
  · have h := gap_lower (n := 12693) (a := (1303371226253 / 1562500000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126202724209 / 50000000000000 : ℝ))
      (E := (cell12693 ⟨19, by decide⟩).energy) (xi := (334267140535667 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12693 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12693]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12693])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12693) (a := (1303371226253 / 1562500000000 : ℝ)) (b := (162279889419 / 100000000000000 : ℝ)) (q := (1126202724209 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12693])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12693]

theorem cert12694_0 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (84076081234757 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252206479427 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨0, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (84076081234757 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252206479427 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_1 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (21010276078809 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563052621751 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨1, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (21010276078809 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563052621751 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_2 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (84006152332709 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (28152680723 / 1250000000000 : ℝ))
      (E := (cell12694 ⟨2, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (84006152332709 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (28152680723 / 1250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_3 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41985612625333 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563054614667 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨3, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41985612625333 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563054614667 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_4 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83936323032793 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450444499629 / 20000000000000 : ℝ))
      (E := (cell12694 ⟨4, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83936323032793 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450444499629 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_5 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41950722821483 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112611323441 / 5000000000000 : ℝ))
      (E := (cell12694 ⟨5, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41950722821483 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (112611323441 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_6 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (335466372181 / 400000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126115247301 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨6, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (335466372181 / 400000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126115247301 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_7 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (838317652039 / 1000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281529308429 / 12500000000000 : ℝ))
      (E := (cell12694 ⟨7, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (838317652039 / 1000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281529308429 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_8 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (20949240520839 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281529806601 / 12500000000000 : ℝ))
      (E := (cell12694 ⟨8, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (20949240520839 / 25000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (281529806601 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_9 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83762183648249 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (56306061451 / 2500000000000 : ℝ))
      (E := (cell12694 ⟨9, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83762183648249 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (56306061451 / 2500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_10 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83727429863389 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126123245097 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨10, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83727429863389 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126123245097 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_11 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (41846350346887 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450450099603 / 20000000000000 : ℝ))
      (E := (cell12694 ⟨11, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (41846350346887 / 50000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (450450099603 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_12 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83657996104583 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252254487997 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨12, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83657996104583 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252254487997 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_13 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83623316061177 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126129233191 / 50000000000000 : ℝ))
      (E := (cell12694 ⟨13, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83623316061177 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (1126129233191 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_14 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (10448582566137 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252262497309 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨14, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (10448582566137 / 12500000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252262497309 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_15 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83554029474061 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563066617569 / 25000000000000 : ℝ))
      (E := (cell12694 ⟨15, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83554029474061 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (563066617569 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_16 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83519422861969 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252270507089 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨16, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83519422861969 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252270507089 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_17 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (16696968131779 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252274496667 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨17, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (16696968131779 / 20000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252274496667 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_18 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83450282831089 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140767406387 / 6250000000000 : ℝ))
      (E := (cell12694 ⟨18, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83450282831089 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (140767406387 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12694_19 : CellCertificate 12694 (443429121988899 / 5000000000000000 : ℝ) (1654674016671983 / 1000000000000000000 : ℝ) (167120082346851 / 5000000000000000 : ℝ)
    (cell12694 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · norm_num [cell12694]
  · have h := gap_lower (n := 12694) (a := (83415749344977 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252282470187 / 100000000000000 : ℝ))
      (E := (cell12694 ⟨19, by decide⟩).energy) (xi := (167120082346851 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12694 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12694]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12694])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12694) (a := (83415749344977 / 100000000000000 : ℝ)) (b := (40566737329 / 25000000000000 : ℝ)) (q := (2252282470187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12694])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12694]

theorem cert12695_0 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (42038033046179 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252083560571 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨0, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (42038033046179 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252083560571 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_1 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (131314202333 / 156250000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126043766891 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨1, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (131314202333 / 156250000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126043766891 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_2 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (84006137830421 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (281511448337 / 12500000000000 : ℝ))
      (E := (cell12695 ⟨2, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (84006137830421 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (281511448337 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_3 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20992802766939 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252095554659 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨3, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20992802766939 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252095554659 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_4 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (8393630916881 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126049780999 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨4, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (8393630916881 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126049780999 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_5 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83901432097459 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563025889797 / 25000000000000 : ℝ))
      (E := (cell12695 ⟨5, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83901432097459 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563025889797 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_6 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (8386657981777 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (4398647567 / 195312500000 : ℝ))
      (E := (cell12695 ⟨6, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (8386657981777 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (4398647567 / 195312500000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_7 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83831752293999 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126055777583 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨7, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83831752293999 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126055777583 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_8 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (20949237372647 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252115569341 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨8, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (20949237372647 / 25000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252115569341 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_9 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41881085686083 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126059773061 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨9, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41881085686083 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126059773061 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_10 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83727417903547 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (140757721909 / 6250000000000 : ℝ))
      (E := (cell12695 ⟨10, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83727417903547 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (140757721909 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_11 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (653849133201 / 781250000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (112606379471 / 5000000000000 : ℝ))
      (E := (cell12695 ⟨11, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (653849133201 / 781250000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (112606379471 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_12 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (8365798477589 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252131553131 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨12, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (8365798477589 / 10000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252131553131 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_13 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (16724661009479 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252135564077 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨13, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (16724661009479 / 20000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252135564077 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_14 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83588649829783 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225213957019 / 10000000000000 : ℝ))
      (E := (cell12695 ⟨14, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83588649829783 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (225213957019 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_15 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83554019088777 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (112607178861 / 5000000000000 : ℝ))
      (E := (cell12695 ⟨15, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83554019088777 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (112607178861 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_16 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (41759706395137 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126073795337 / 50000000000000 : ℝ))
      (E := (cell12695 ⟨16, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (41759706395137 / 50000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (1126073795337 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_17 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (1669696618007 / 2000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252151557607 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨17, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (1669696618007 / 2000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252151557607 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_18 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (83450273385257 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252155541199 / 100000000000000 : ℝ))
      (E := (cell12695 ⟨18, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (83450273385257 / 100000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (2252155541199 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12695_19 : CellCertificate 12695 (221707570998419 / 2500000000000000 : ℝ) (827271816596219 / 500000000000000000 : ℝ) (83553298316549 / 2500000000000000 : ℝ)
    (cell12695 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · norm_num [cell12695]
  · have h := gap_lower (n := 12695) (a := (4170787010571 / 5000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563039886557 / 25000000000000 : ℝ))
      (E := (cell12695 ⟨19, by decide⟩).energy) (xi := (83553298316549 / 2500000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12695 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12695]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12695])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12695) (a := (4170787010571 / 5000000000000 : ℝ)) (b := (40563502823 / 25000000000000 : ℝ)) (q := (563039886557 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12695])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12695]

theorem cert12696_0 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (84076050952347 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (562990173699 / 25000000000000 : ℝ))
      (E := (cell12696 ⟨0, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (84076050952347 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (562990173699 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_1 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (84041074673353 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1125982345769 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨1, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (84041074673353 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1125982345769 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_2 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16801224666089 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450393730609 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨2, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16801224666089 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450393730609 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_3 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41985598443559 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1125986351961 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨3, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41985598443559 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1125986351961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_4 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83936295307059 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251976679187 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨4, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83936295307059 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251976679187 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_5 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41950709277073 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251980702953 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨5, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41950709277073 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251980702953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_6 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41933283296223 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251984667467 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨6, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41933283296223 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251984667467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_7 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16766347877243 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281498587053 / 12500000000000 : ℝ))
      (E := (cell12696 ⟨7, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16766347877243 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281498587053 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_8 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83796936899897 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450398536293 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨8, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83796936899897 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450398536293 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_9 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83762159098123 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251996687853 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨9, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83762159098123 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2251996687853 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_10 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41863702972853 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126000332303 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨10, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41863702972853 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126000332303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_11 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (16738535481529 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252004676533 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨11, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (16738535481529 / 20000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252004676533 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_12 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41828986724561 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126004336051 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨12, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41828986724561 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126004336051 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_13 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83623294035499 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252012657557 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨13, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83623294035499 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252012657557 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_14 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41794319566159 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126008348517 / 50000000000000 : ℝ))
      (E := (cell12696 ⟨14, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41794319566159 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (1126008348517 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_15 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (41777004352651 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252020680029 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨15, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (41777004352651 / 50000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252020680029 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_16 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (1670388054407 / 2000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252024670163 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨16, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (1670388054407 / 2000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252024670163 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_17 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (83484821143539 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281503584087 / 12500000000000 : ℝ))
      (E := (cell12696 ⟨17, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (83484821143539 / 100000000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (281503584087 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_18 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (4074719919 / 4882812500 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252032692649 / 100000000000000 : ℝ))
      (E := (cell12696 ⟨18, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (4074719919 / 4882812500 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (2252032692649 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12696_19 : CellCertificate 12696 (886802328238787 / 10000000000000000 : ℝ) (1654413270258947 / 1000000000000000000 : ℝ) (334186226251971 / 10000000000000000 : ℝ)
    (cell12696 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · norm_num [cell12696]
  · have h := gap_lower (n := 12696) (a := (521348319247 / 625000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450407335309 / 20000000000000 : ℝ))
      (E := (cell12696 ⟨19, by decide⟩).energy) (xi := (334186226251971 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12696 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12696]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12696])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12696) (a := (521348319247 / 625000000000 : ℝ)) (b := (32448215069 / 20000000000000 : ℝ)) (q := (450407335309 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12696])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12696]

theorem cert12697_0 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (3363041432589 / 4000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251837824291 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨0, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (3363041432589 / 4000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251837824291 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_1 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (42020529927967 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125920922303 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨1, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (42020529927967 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125920922303 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_2 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (42003054416389 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125922915229 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨2, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (42003054416389 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125922915229 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_3 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83971182708751 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (90073993943 / 4000000000000 : ℝ))
      (E := (cell12697 ⟨3, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83971182708751 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (90073993943 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_4 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83936281447541 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562963462427 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨4, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83936281447541 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562963462427 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_5 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41950702506513 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251857842189 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨5, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41950702506513 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251857842189 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_6 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (20966638342319 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225186183409 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨6, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (20966638342319 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225186183409 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_7 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83831726480547 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251865833231 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨7, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83831726480547 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251865833231 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_8 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (20949231077821 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (90074793887 / 4000000000000 : ℝ))
      (E := (cell12697 ⟨8, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (20949231077821 / 25000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (90074793887 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_9 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83762146826119 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251873825213 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨9, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83762146826119 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251873825213 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_10 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (16745478797973 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251877832381 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨10, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (16745478797973 / 20000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251877832381 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_11 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (3347706630701 / 4000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251881817419 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨11, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (3347706630701 / 4000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251881817419 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_12 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41828981062139 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225188584491 / 10000000000000 : ℝ))
      (E := (cell12697 ⟨12, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41828981062139 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (225188584491 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_13 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83623283025489 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562972465763 / 25000000000000 : ℝ))
      (E := (cell12697 ⟨13, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83623283025489 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (562972465763 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_14 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83588628436701 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125946909851 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨14, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83588628436701 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125946909851 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_15 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83553998323637 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251897836863 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨15, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83553998323637 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251897836863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_16 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41759696326099 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125950930961 / 50000000000000 : ℝ))
      (E := (cell12697 ⟨16, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41759696326099 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (1125950930961 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_17 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (83484811388461 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450381168387 / 20000000000000 : ℝ))
      (E := (cell12697 ⟨17, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (83484811388461 / 100000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (450381168387 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_18 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41725127249339 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251909840081 / 100000000000000 : ℝ))
      (E := (cell12697 ⟨18, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41725127249339 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (2251909840081 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12697_19 : CellCertificate 12697 (443387188356063 / 5000000000000000 : ℝ) (827141463933327 / 500000000000000000 : ℝ) (334159263649849 / 10000000000000000 : ℝ)
    (cell12697 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · norm_num [cell12697]
  · have h := gap_lower (n := 12697) (a := (41707860974639 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (140744616321 / 6250000000000 : ℝ))
      (E := (cell12697 ⟨19, by decide⟩).energy) (xi := (334159263649849 / 10000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12697 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12697]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12697])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12697) (a := (41707860974639 / 50000000000000 : ℝ)) (b := (40557035369 / 25000000000000 : ℝ)) (q := (140744616321 / 6250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12697])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12697]

theorem cert12698_0 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (84076020679489 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (225171500687 / 10000000000000 : ℝ))
      (E := (cell12698 ⟨0, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (84076020679489 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (225171500687 / 10000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_1 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16808209008173 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450343798597 / 20000000000000 : ℝ))
      (E := (cell12698 ⟨1, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16808209008173 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450343798597 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_2 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (84006094337421 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (281465375403 / 12500000000000 : ℝ))
      (E := (cell12698 ⟨2, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (84006094337421 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (281465375403 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_3 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16794233706531 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (4503454093 / 200000000000 : ℝ))
      (E := (cell12698 ⟨3, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16794233706531 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (4503454093 / 200000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_4 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16787253518051 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251731015661 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨4, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16787253518051 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251731015661 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_5 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (839013914741 / 1000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251735034823 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨5, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (839013914741 / 1000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251735034823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_6 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83866540148261 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (90069559849 / 4000000000000 : ℝ))
      (E := (cell12698 ⟨6, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83866540148261 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (90069559849 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_7 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16766342715399 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251743023563 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨7, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16766342715399 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251743023563 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_8 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83796911724749 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (90069880339 / 4000000000000 : ℝ))
      (E := (cell12698 ⟨8, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83796911724749 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (90069880339 / 4000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_9 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83762134556153 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (70367219257 / 3125000000000 : ℝ))
      (E := (cell12698 ⟨9, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83762134556153 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (70367219257 / 3125000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_10 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41863691018013 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251754995823 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨10, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41863691018013 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251754995823 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_11 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (41846327064683 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125879506041 / 50000000000000 : ℝ))
      (E := (cell12698 ⟨11, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (41846327064683 / 50000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (1125879506041 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_12 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83657950801357 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251763013467 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨12, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83657950801357 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251763013467 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_13 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (20905818004341 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (112588350311 / 5000000000000 : ℝ))
      (E := (cell12698 ⟨13, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (20905818004341 / 25000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (112588350311 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_14 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83588617742931 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450354199267 / 20000000000000 : ℝ))
      (E := (cell12698 ⟨14, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83588617742931 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (450354199267 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_15 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83553987943781 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251775047723 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨15, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83553987943781 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251775047723 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_16 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (10439922823227 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562944762397 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨16, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (10439922823227 / 12500000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562944762397 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_17 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (16696960327023 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251783007119 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨17, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (16696960327023 / 20000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251783007119 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_18 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83450245057931 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251787041727 / 100000000000000 : ℝ))
      (E := (cell12698 ⟨18, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83450245057931 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (2251787041727 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12698_19 : CellCertificate 12698 (886746429412687 / 10000000000000000 : ℝ) (1654152606010703 / 1000000000000000000 : ℝ) (167066152729327 / 5000000000000000 : ℝ)
    (cell12698 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · norm_num [cell12698]
  · have h := gap_lower (n := 12698) (a := (83415712820693 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562947760437 / 25000000000000 : ℝ))
      (E := (cell12698 ⟨19, by decide⟩).energy) (xi := (167066152729327 / 5000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12698 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12698]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12698])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12698) (a := (83415712820693 / 100000000000000 : ℝ)) (b := (40553802421 / 25000000000000 : ℝ)) (q := (562947760437 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12698])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12698]

theorem cert12699_0 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨0, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (84076005546641 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562898060633 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨0, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨0, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (84076005546641 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562898060633 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_1 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨1, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (42020515114071 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251596252347 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨1, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨1, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (42020515114071 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251596252347 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_2 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨2, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (84006079844373 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (5629000573 / 250000000000 : ℝ))
      (E := (cell12699 ⟨2, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨2, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (84006079844373 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (5629000573 / 250000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_3 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨3, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83971154358829 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125802119909 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨3, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨3, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83971154358829 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125802119909 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_4 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨4, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83936253735199 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251608234953 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨4, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨4, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83936253735199 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251608234953 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_5 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨5, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41950688968683 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251612222931 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨5, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨5, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41950688968683 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251612222931 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_6 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨6, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (419332634647 / 500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251616269773 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨6, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨6, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (419332634647 / 500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251616269773 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_7 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨7, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83831700675559 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (112581013371 / 5000000000000 : ℝ))
      (E := (cell12699 ⟨7, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨7, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83831700675559 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (112581013371 / 5000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_8 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨8, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (8379689914029 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562906055841 / 25000000000000 : ℝ))
      (E := (cell12699 ⟨8, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨8, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (8379689914029 / 10000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (562906055841 / 25000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_9 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨9, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83762122288227 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125814130443 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨9, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨9, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83762122288227 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125814130443 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_10 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨10, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41863685042093 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125816106491 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨10, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨10, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41863685042093 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125816106491 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_11 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨11, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83692642493169 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125818130261 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨11, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨11, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83692642493169 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125818130261 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_12 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨12, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (2091448487009 / 2500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251640235863 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨12, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨12, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (2091448487009 / 2500000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251640235863 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_13 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨13, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (20905815252781 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450328852281 / 20000000000000 : ℝ))
      (E := (cell12699 ⟨13, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨13, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (20905815252781 / 25000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (450328852281 / 20000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_14 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨14, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83588607051007 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125824113467 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨14, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨14, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83588607051007 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125824113467 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_15 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨15, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83553977565733 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251652254451 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨15, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨15, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83553977565733 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251652254451 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_16 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨16, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (16703874504241 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251656233159 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨16, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨16, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (16703874504241 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251656233159 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_17 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨17, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (41742395941751 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281457528307 / 12500000000000 : ℝ))
      (E := (cell12699 ⟨17, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨17, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (41742395941751 / 50000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (281457528307 / 12500000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_18 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨18, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (83450235618879 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251664239357 / 100000000000000 : ℝ))
      (E := (cell12699 ⟨18, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨18, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (83450235618879 / 100000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (2251664239357 / 100000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

theorem cert12699_19 : CellCertificate 12699 (443359243169733 / 5000000000000000 : ℝ) (1654022304686243 / 1000000000000000000 : ℝ) (33410535167721 / 1000000000000000 : ℝ)
    (cell12699 ⟨19, by decide⟩) := by
  constructor
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · norm_num [cell12699]
  · have h := gap_lower (n := 12699) (a := (16683140738753 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125834138319 / 50000000000000 : ℝ))
      (E := (cell12699 ⟨19, by decide⟩).energy) (xi := (33410535167721 / 1000000000000000 : ℝ))
      (u := (286 / 100000 : ℝ)) (d := (cell12699 ⟨19, by decide⟩).cutoff)
      (by norm_num) (by norm_num [cell12699]) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [cell12699])
    exact lt_of_lt_of_le (by norm_num) h
  · exact mass_bound_rational (n := 12699) (a := (16683140738753 / 20000000000000 : ℝ)) (b := (5068821249 / 3125000000000 : ℝ)) (q := (1125834138319 / 50000000000000 : ℝ))
      (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [cell12699])
      (by norm_num [BstLean.Part253.rotationPowerCap])
  · norm_num [cell12699]

end BstLean.Part268
